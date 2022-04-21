//! Some tricks to provide borrowed iterators in the Python bindings.
//! Inspired by the discussion in https://github.com/PyO3/pyo3/issues/1085
//! and the approach proposed in https://gist.github.com/b05902132/de18debe9039473aa9b0bed6b48436c8

use pyo3::prelude::*;
use pyo3::{IntoPy, Py, PyAny, PyClass, PyObject, PyRef, Python};

pub trait IteratorOfPyObject {
    fn next_py(&mut self, py: Python) -> Option<PyObject>;

    fn close(&mut self, py: Python);
}

#[pyclass(unsendable)]
pub struct BoxedPyIterator(Box<dyn IteratorOfPyObject>);

#[pymethods]
impl BoxedPyIterator {
    fn __iter__(slf: PyRef<Self>) -> PyRef<Self> {
        slf
    }

    fn __next__(&mut self, py: Python) -> Option<PyObject> {
        self.0.next_py(py)
    }

    fn close(&mut self, py: Python) {
        self.0.close(py);
    }

    // FIXME: should we handle __traverse__ and __clear__?
}

impl BoxedPyIterator {
    pub fn new<T: 'static + IteratorOfPyObject>(it: T) -> Self {
        Self(Box::new(it))
    }
}

/// Hold a borrowed reference to a field inside a PyClass instance.
/// This is used in particular to generate borrowed iterators.
///
/// The owner object cannot be modified as long as the borrow is active,
/// so this should be dropped or released as soon as possible
pub struct PyBorrowed<T: PyClass + 'static, R> {
    // WARNING: the declaration order corresponds to the drop order and must be
    // maintained to ensure that we keep the object longer than borrowed references!
    /// The inner borrowed data
    inner: Option<R>,

    /// An open PyRef blocking concurrent modifications on the owner
    pyref: Option<PyRef<'static, T>>,

    /// Keep a copy of the owner object (managed by Python), ensuring that it is not dropped
    _owner: Py<T>,
}

impl<T: PyClass + 'static, R> PyBorrowed<T, R> {
    pub fn new<F>(py: Python, owner: Py<T>, f: F) -> Self
    where
        F: Fn(&'static T) -> R,
    {
        // SAFETY note:
        //   Use std::mem::transmute to artificially extends the lifetime and trick the borrow checker.
        //   This extension is safe as long as we keep the owner longer than these extended references.
        let pyref: PyRef<'static, T> = unsafe { std::mem::transmute(owner.borrow(py)) };
        let eref: &'static T = unsafe { std::mem::transmute(&*pyref) };
        let inner = f(eref);
        Self {
            _owner: owner,
            pyref: Some(pyref),
            inner: Some(inner),
        }
    }

    pub fn borrow(&self) -> Option<&R> {
        self.inner.as_ref()
    }

    pub fn borrow_mut(&mut self) -> Option<&mut R> {
        self.inner.as_mut()
    }

    /// Release the held reference to make the owner mutable again.
    /// This can happen during drop or be called in advance to avoid waiting
    /// for the Python garbage collector in some corner cases
    pub fn release(&mut self) {
        if self.pyref.is_some() {
            println!("explicit release for a borrowed item");
        }
        // release borrowed fields in the right order!
        self.inner = None;
        self.pyref = None;
    }
}

impl<T: PyClass + 'static, R> Drop for PyBorrowed<T, R> {
    fn drop(&mut self) {
        // This is probably not necessary as we could rely on rust's guaranteed drop order
        println!("Dropping a borrowed item");
        self.release();
    }
}

impl<T: PyClass + 'static, I: IntoPy<Py<PyAny>>, R: Iterator<Item = I>> IteratorOfPyObject
    for PyBorrowed<T, R>
{
    /// Get the next object and release the held borrow when the end of the iterator is reached
    fn next_py(&mut self, py: Python) -> Option<PyObject> {
        let next = match self.borrow_mut() {
            None => return None,
            Some(v) => v.next().map(|v| v.into_py(py)),
        };

        if next.is_none() {
            self.release();
        }
        next
    }

    fn close(&mut self, _: Python) {
        self.release();
    }
}

pub fn borrow_iterator<
    T: PyClass + 'static,
    I: IntoPy<Py<PyAny>>,
    R: 'static + Iterator<Item = I>,
    F: Fn(&'static T) -> R,
>(
    py: Python,
    obj: Py<T>,
    f: F,
) -> Option<BoxedPyIterator> {
    Some(BoxedPyIterator::new(PyBorrowed::new(py, obj, f)))
}
