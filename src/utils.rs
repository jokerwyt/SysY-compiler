use std::{cell::{Ref, RefCell, RefMut}, collections::HashMap};

use uuid::Uuid;

// pub mod arena;

// pub struct RcRef<T> {
//   data: Rc<RefCell<T>>,
// }

// impl<T> Clone for RcRef<T> {
//     fn clone(&self) -> Self {
//         Self { data: self.data.clone() }
//     }
// }

// impl <T> RcRef<T> {
//   pub fn new(data: T) -> Self {
//     Self {
//       data: Rc::new(RefCell::new(data)),
//     }
//   }

//   pub fn borrow(&self) -> std::cell::Ref<T> {
//     self.data.borrow()
//   }

//   pub fn borrow_mut(&self) -> std::cell::RefMut<T> {
//     self.data.borrow_mut()
//   }
// }

pub struct UuidMapper<T> {
  pub data: HashMap<Uuid, RefCell<T>>,
}

impl<T: UuidOwner> UuidMapper<T> {
  pub fn new() -> Self {
    Self {
      data: HashMap::new(),
    }
  }

  pub fn borrow(&self, id: &Uuid) -> Option<Ref<'_, T>> {
    let a = self.data.get(&id);
    if a.is_none() {
      None
    } else {
      let t = a.unwrap();
      Some(t.borrow())
    }
  }

  pub fn borrow_mut(&self, id: &Uuid) -> Option<RefMut<'_, T>> {
    let a = self.data.get(&id);
    if a.is_none() {
      None
    } else {
      let t = a.unwrap();
      Some(t.borrow_mut())
    }
  }

  pub fn insert(&mut self, data: T) -> Uuid {
    let id = data.id();
    if self.data.contains_key(&id) {
      panic!("GlobalMapper: id already exists");
    }
    self.data.insert(id, RefCell::new(data));
    id
  }
}

pub trait UuidOwner {
  fn id(&self) -> Uuid;
}

/// A macro generates a thread_local static variable and the submit functions.
#[macro_export]
macro_rules! global_mapper {
  ($name:ident, $type:ty) => {
    thread_local! {
      static $name: RefCell<UuidMapper<$type>> = RefCell::new(UuidMapper::new());
    }

    pub fn submit<F, R>(id: Uuid, closure: F) -> R
    where 
      F: FnOnce(&mut $type) -> R
    {
      $name.with(|tables| {
        let tables = tables.borrow_mut();
        let mut table = tables.borrow_mut(&id).unwrap();
        closure(&mut table)
      })
    }
  };
}