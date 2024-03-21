use std::cell::RefCell;
use std::rc::Rc;
use std::collections::HashMap;

pub struct WWW {
    name: Vec<String>
}

#[derive(Clone)]
pub enum hello {
    vari(Rc<RefCell<WWW>>)
}

#[derive(Debug)]
pub enum hello2 {
    vari(String)
}

#[derive(Clone)]
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


fn main() {
    let a: RefCell<hello2> = RefCell::new(hello2::vari("aaa".to_string()));
    let b = a.borrow();
    a.replace(hello2::vari("bbb".to_string()));
    println!("b = {:?}", b);
}
