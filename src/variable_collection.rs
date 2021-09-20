use crate::*;

use once_cell::sync::Lazy;
use regex::Regex;
use slab::Slab;
use std::fmt;
use std::str::FromStr;

static RE_UID: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"^(_[01-9_]*)?[a-zA-Z][a-zA-Z01-9_]*$").unwrap());

static NAME_SEPARATORS: [char; 4] = [' ', ',', ';', '&'];

/// Associate (group of) variables with their name in a collection.
///
/// Unlike variables, the component is tight to a collection of variables.
/// This object borrows internal data from the collection.
#[derive(Clone, Copy)]
pub enum Component<'a> {
    /// A single Boolean variable
    Single(&'a str, Variable),
    /// A group of related variables
    Group(&'a str, &'a [Variable]),
}

/// A collection of named variables.
///
/// Adding a new name to the collection triggers the creation of a variable associated to a unique integer UID
/// (using successive UIDs for better scalability). Variables can then be used independently of the collection.
/// A request with an existing name allows to recover a variable with the same UID.
///
/// The name of a variable can be changed (then the old name can no longer be used to recover this variable).
/// Variables can be removed from the collection, in which case their internal UIDs can be reused for new variables.
///
/// The collection can be used to retrieve the name associated with existing variables, which is especially useful
/// to display Boolean expressions.
///
/// # Associated variables
///
/// By default, each variable created in a [collection of variables](VariableCollection) is associated to a specific name and
/// independent from other variables in the same collection. The collection can also be used to create subgroups of
/// associated variables, related to the same core variable. The name associated with the core variable is then shared
/// with all associated variables, identified within the subgroup by an extra tag.
///
/// While the collection keeps track of these subgroups, each variable of the collection (isolated, core or associated)
/// remains a regular Boolean variable. Subgroups could be used to represent multivalued components or other kind
/// of relations between the variables, but this interpretation is left for the user of the API.
///
/// ```
/// use bokit::VariableCollection;
/// # use bokit::BokitError;
/// # fn main() -> Result<(), BokitError> {
///
/// let mut variables = VariableCollection::default();
///
/// // Create a core variable and an associated one
/// let v1 = variables.add("A")?;
/// let v1_1 = variables.associate(v1, 1)?;
///
/// // Use any associated variable to retrieve a component describing the group
/// let c1 = variables.get_component(v1)?;
///
/// // Display the two associated variables
/// println!("{} {}", variables.named(&v1), variables.named(&v1_1));
/// # Ok(())
/// # }
/// ```
#[derive(Clone, Default, Debug)]
pub struct VariableCollection {
    /// The list of variables
    blocks: Slab<VariableBlock>,

    /// Groups of associated variables
    groups: Slab<Subgroup>,

    /// Find a variable by name
    name2uid: HashMap<String, Variable>,
}

/// A named rule associates a rule to a variable collection to provide prettier display output
struct NamedRule<'a> {
    namer: &'a VariableCollection,
    rule: &'a dyn Rule,
}

/// Information about a variable in the list of blocks
#[derive(Clone, Debug)]
pub enum VariableBlock {
    /// An isolated Boolean variable
    Single(String),
    /// An associated variable, pointing to its subgroup and rank
    Associated(usize, usize),
}

#[derive(Clone, Debug)]
pub struct Subgroup {
    name: String,
    members: Vec<Variable>,
}

impl Subgroup {
    pub fn new(name: String) -> Self {
        Self {
            name,
            members: Vec::default(),
        }
    }
}

impl VariableCollection {
    /// Retrieve a named variable or create it if needed.
    ///
    /// If a variable with this name already exists, return it without any change in the collection.
    /// Otherwise, create a new Variable associated to the desired name.
    ///
    /// Returns an error if the name is invalid, in this case the collection is not modified.
    /// Panics if the new variable can not be created (usize or memory overflow).
    pub fn add(&mut self, name: &str) -> Result<Variable, BokitError> {
        if let Some(var) = self.name2uid.get(name) {
            return Ok(*var);
        }

        // Reject invalid names
        if !RE_UID.is_match(name) {
            return Err(BokitError::InvalidName(name.into()));
        }

        // Create and insert the new block
        let block = VariableBlock::Single(name.into());
        let var = self.blocks.insert(block).into();
        self.name2uid.insert(name.into(), var);
        Ok(var)
    }

    /// Retrieve an associated variable, create it if needed.
    ///
    /// If the associated variable exists, return it without any change to the collection.
    /// Otherwise, create and return the associated variable.
    ///
    /// Note that
    /// * If the anchor variable is a single variable, it will become part of a subgroup.
    /// * Any variable of a group can be used as anchor, the index is always a global index in the subgroup.
    /// * Subgroups don't allow gaps: intermediate associated variables can be created to reach the desired index.
    ///
    /// Returns an error if the core variable is not part of the collection.
    /// Panics if the new variable can not be created (usize or memory overflow)
    pub fn associate(&mut self, v: impl VariableID, idx: usize) -> Result<Variable, BokitError> {
        let v = v.into();
        match self.blocks.get(v.uid()) {
            None => Err(BokitError::NoSuchVariable(v)),
            Some(VariableBlock::Associated(gid, vid)) => {
                if *vid == idx {
                    return Ok(v);
                }
                let gid = *gid;
                Ok(self._associate_to_group(gid, idx))
            }
            Some(VariableBlock::Single(name)) => {
                if idx == 0 {
                    return Ok(v);
                }
                let name = name.clone();
                let gid = self._create_subgroup(name, v);
                self.blocks[v.uid()] = VariableBlock::Associated(gid, 0);
                Ok(self._associate_to_group(gid, idx))
            }
        }
    }

    fn _create_subgroup(&mut self, name: String, var: Variable) -> usize {
        let mut grp = Subgroup::new(name);
        grp.members.push(var);
        self.groups.insert(grp)
    }

    /// Retrieve a variable associated to a group, extending the group if needed
    fn _associate_to_group(&mut self, gid: usize, idx: usize) -> Variable {
        let grp = self.groups.get_mut(gid).unwrap();

        for i in grp.members.len()..(idx + 1) {
            let var = self.blocks.insert(VariableBlock::Associated(gid, i)).into();
            grp.members.push(var);
        }

        *grp.members.get(idx).unwrap()
    }

    /// Get the component corresponding to a given variable.
    ///
    /// The component indicates if a variable is a regular Boolean variable ([Component::Single])
    /// or part of a subgroup ([Component::Group]). In this case, return the same variables
    ///for all members of the subgroup.
    ///
    /// Returns an error if the variable is not part of the collection.
    pub fn get_component(&self, v: impl VariableID) -> Result<Component, BokitError> {
        let v = v.into();
        match self.blocks.get(v.uid()) {
            None => Err(BokitError::NoSuchVariable(v)),
            Some(VariableBlock::Single(name)) => Ok(Component::Single(name, v)),
            Some(VariableBlock::Associated(gid, _)) => {
                let grp = &self.groups[*gid];
                Ok(Component::Group(&grp.name, &grp.members))
            }
        }
    }

    /// Rename a variable identified by its old name and retrieve the corresponding Variable.
    ///
    /// Returns an error if the old name does not exist in the collection or if the new one is either
    /// invalid or already associated to another variable. Renaming to the same name is accepted
    /// (in this case, the collection is not changed)
    pub fn rename(&mut self, old: &str, name: &str) -> Result<Variable, BokitError> {
        let var = self.get_variable(old)?;
        self.set_name(var, name)?;
        Ok(var)
    }

    /// Parse an expression and create new variables as needed
    ///
    /// Returns an error if the text is not a valid expression, and in particular
    /// if some variable names are invalid
    pub fn parse_expression_with_new_variables(&mut self, text: &str) -> Result<Expr, BokitError> {
        parse::parse_expression(&mut |name| self.add(name), text)
    }

    /// Create a set of variables of this collection based on their list of names
    ///
    /// Returns an error if one of the names is not part of the collection, in particular if it in invalid
    pub fn parse_variable_set(
        &self,
        descr: &str,
        sep: Option<&[char]>,
    ) -> Result<VarSet, BokitError> {
        let separators = sep.unwrap_or(&NAME_SEPARATORS);
        let mut vs = VarSet::default();
        for name in descr.split(separators) {
            vs.insert(self.get_variable(name)?);
        }
        Ok(vs)
    }

    /// Get the number of assigned Variables
    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    /// Return whether there are no variables in this collection
    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    /// Remove a given variable.
    ///
    /// This operation does not fail as it ignored variable which are not part of the collection
    pub fn remove_variable(&mut self, var: impl VariableID) {
        if !self.blocks.contains(var.uid()) {
            return;
        }
        // Free the slot, if it contained a variable do some additional cleanup
        match self.blocks.remove(var.uid()) {
            VariableBlock::Single(name) => {
                self.name2uid.remove(&name);
            }
            VariableBlock::Associated(gid, idx) => {
                self._remove_from_group(gid, idx);
            }
        }
    }

    /// Remove an associated variable from a group.
    ///
    /// We assume that the variable is no longer registered as associated to this group
    /// (in most case this happens in the cleanup phase of variable removal).
    fn _remove_from_group(&mut self, gid: usize, idx: usize) {
        let grp = self.groups.get_mut(gid).unwrap();
        grp.members.remove(idx);
        if grp.members.len() == 1 {
            // This should now be a single variable
            self.blocks[grp.members[0].uid()] = VariableBlock::Single(grp.name.clone());
            self.groups.remove(gid);
        } else {
            for (cur, v) in grp.members.iter().enumerate() {
                self.blocks[v.uid()] = VariableBlock::Associated(gid, cur)
            }
        }
    }

    /// Assign a new name to a variable.
    ///
    /// Returns an error if the variable is not part of the collection or if the new name
    /// is either invalid or already associated to another variable.
    pub fn set_name(&mut self, v: impl VariableID, name: &str) -> Result<(), BokitError> {
        let v = v.into();
        if !self.contains(v) {
            return Err(BokitError::NoSuchVariable(v));
        }

        // Reject invalid names
        if !RE_UID.is_match(name) {
            return Err(BokitError::InvalidName(name.into()));
        }

        // Detect conflicts or unchanged names
        if let Ok(existing) = self.get_variable(name) {
            if existing == v {
                return Ok(());
            }
            return Err(BokitError::ConflictingName(String::from(name)));
        }

        // All consistency checks passed, do the actual update
        let old_name = match &mut self.blocks[v.uid()] {
            VariableBlock::Single(s) => s,
            VariableBlock::Associated(gid, _) => &mut self.groups[*gid].name,
        };

        self.name2uid.insert(name.into(), v);
        self.name2uid.remove(old_name);
        *old_name = name.into();
        Ok(())
    }

    /// Check if a variable is part of the collection
    pub fn contains(&self, var: impl VariableID) -> bool {
        self.blocks.get(var.uid()).is_some()
    }

    /// Check if all variables are part of this collection
    pub fn contains_all<A: VariableID, T: IntoIterator<Item = A>>(&self, col: T) -> bool {
        !col.into_iter().any(|v| !self.contains(v))
    }

    /// Check if all variables of the set are part of this collection
    pub fn contains_set(&self, vs: &VarSet) -> bool {
        // TODO: replace with a dedicated bitwise test
        self.contains_all(vs)
    }

    /// Check if a name is part of the collection
    pub fn contains_name(&self, name: &str) -> bool {
        self.name2uid.contains_key(name)
    }

    /// Check if all variables names are part of this collection
    pub fn contains_all_names<'a, T: IntoIterator<Item = &'a str>>(&self, col: T) -> bool {
        !col.into_iter().any(|v| !self.contains_name(v))
    }

    /// Parse an expression using variable names
    pub fn parse_expression(&self, text: &str) -> Result<Expr, BokitError> {
        parse::parse_expression(&mut |name| self.get_variable(name), text)
    }

    /// Parse a state using variable names from this set
    pub fn get_state(&self, state_string: &str) -> Result<State, BokitError> {
        let mut state = State::default();
        for name in state_string.split(&[',', ' ', ';'][..]) {
            if name.is_empty() {
                continue;
            }
            state.activate(self.get_variable(name)?);
        }
        Ok(state)
    }

    /// Apply variable names from this collection to a rule.
    ///
    /// This operation is only useful to display rules (especially expressions) or variables.
    pub fn named<'a>(&'a self, rule: &'a impl Rule) -> impl fmt::Display + 'a {
        NamedRule { namer: self, rule }
    }

    /// Check that a rule uses only variables included in this collection
    pub fn check_rule(&self, rule: &dyn Rule) -> Result<(), BokitError> {
        let regulators = rule.get_regulators();
        // TODO: cache variables for faster check?
        for i in regulators.iter() {
            if !self.contains(i) {
                return Err(BokitError::NoSuchVariable(i));
            }
        }
        Ok(())
    }

    /// Insert the name of a variable during a display operation.
    ///
    /// The default implementation generates a generic name based on the variable UID.
    pub fn format_variable(&self, f: &mut fmt::Formatter, var: impl VariableID) -> fmt::Result {
        match self.blocks.get(var.uid()) {
            None => write!(f, "{}", var.into()),
            Some(VariableBlock::Single(s)) => write!(f, "{}", s),
            Some(VariableBlock::Associated(gid, t)) => {
                write!(f, "{}:{}", self.groups.get(*gid).unwrap().name, t)
            }
        }
    }

    /// Search a variable with the given name
    pub fn get_variable(&self, name: &str) -> Result<Variable, BokitError> {
        match self.name2uid.get(name) {
            None => match Variable::from_str(name) {
                Ok(v) => Ok(v),
                Err(_) => Err(BokitError::NoSuchVariableName(String::from(name))),
            },
            Some(var) => Ok(*var),
        }
    }

    /// Iterate on all variables of this collection
    pub fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Variable> + 'a> {
        self.into_iter()
    }

    /// Iterate on all components of this collection
    pub fn iter_components<'a>(&'a self) -> Box<dyn Iterator<Item = Component> + 'a> {
        Box::new(self.blocks.iter().filter_map(move |(idx, v)| match v {
            VariableBlock::Single(name) => Some(Component::Single(name, idx.into())),
            VariableBlock::Associated(gid, tag) => {
                if *tag > 0 {
                    return None;
                }
                let grp = &self.groups[*gid];
                Some(Component::Group(&grp.name, &grp.members))
            }
        }))
    }
}

impl<'a> IntoIterator for &'a VariableCollection {
    type Item = Variable;
    type IntoIter = Box<dyn Iterator<Item = Variable> + 'a>;

    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.blocks.iter().map(|(idx, _)| idx.into()))
    }
}

impl fmt::Display for NamedRule<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.rule.fmt_rule(f, self.namer)
    }
}
