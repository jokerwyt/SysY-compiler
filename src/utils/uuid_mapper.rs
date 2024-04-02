use std::{
  cell::{Ref, RefCell, RefMut},
  collections::HashMap,
};

use uuid::Uuid;

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

  pub fn register(&mut self, data: T) -> Uuid {
    let id = data.id();
    if self.data.contains_key(&id) {
      panic!("UuidMapper: the id to register already exists");
    }
    self.data.insert(id, RefCell::new(data));
    id
  }
}

pub trait UuidOwner {
  fn id(&self) -> Uuid;
}

/// A macro generates a thread_local static variable and the submit functions.
///
#[macro_export]
macro_rules! global_mapper {
  ($name:ident, $read_func_name:ident, $write_func_name:ident, $register_name:ident, $value_type:ty) => {
    thread_local! {
      static $name: std::cell::RefCell<crate::utils::uuid_mapper::UuidMapper<$value_type>>
        = std::cell::RefCell::new(crate::utils::uuid_mapper::UuidMapper::new());
    }

    /// Submit a closure to the UuidMapper with the given id.
    /// Returns Err if the id does not exist.
    pub fn $read_func_name<F, R>(id: &Uuid, closure: F) -> R
    where
      F: FnOnce(&$value_type) -> R,
    {
      $name.with(|values| {
        let values = values.borrow();
        let value = values.borrow(id);
        if let Some(value) = value {
          return closure(&value);
        } else {
          panic!("UuidMapper {}: id {} does not exist", stringify!($name), id);
        }
      })
    }

    pub fn $write_func_name<F, R>(id: &Uuid, closure: F) -> R
    where
      F: FnOnce(&mut $value_type) -> R,
    {
      $name.with(|values| {
        let values = values.borrow_mut();
        let value = values.borrow_mut(id);
        if let Some(mut value) = value {
          return closure(&mut value);
        } else {
          panic!("UuidMapper {}: id {} does not exist", stringify!($name), id);
        }
      })
    }

    /// Register a new value and return its id.
    ///
    /// # Panic
    /// panic if the id already exists.
    pub fn $register_name(data: $value_type) -> Uuid {
      $name.with(|values| {
        let mut values = values.borrow_mut();
        values.register(data)
      })
    }
  };
}
