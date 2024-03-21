use std::{cell::RefCell, rc::Rc};

pub mod arena;

pub struct RcRef<T> {
  data: Rc<RefCell<T>>,
}

impl <T> RcRef<T> {
  pub fn new(data: T) -> Self {
    Self {
      data: Rc::new(RefCell::new(data)),
    }
  }

  pub fn borrow(&self) -> std::cell::Ref<T> {
    self.data.borrow()
  }

  pub fn borrow_mut(&self) -> std::cell::RefMut<T> {
    self.data.borrow_mut()
  }
}
