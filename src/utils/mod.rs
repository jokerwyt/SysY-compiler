pub mod dfs;
pub mod interpreter;
pub mod uuid_mapper;

pub type Res = Result<(), String>;

/// A macro to create wrapper for a given type
#[macro_export]
macro_rules! define_wrapper {
  ($name:ident, $inner:ty) => {
    #[derive(Clone)]
    pub struct $name(pub $inner);

    impl std::ops::Deref for $name {
      type Target = $inner;
      fn deref(&self) -> &Self::Target {
        &self.0
      }
    }

    impl Into<$inner> for $name {
      fn into(self) -> $inner {
        self.0
      }
    }
    impl Into<$name> for $inner {
      fn into(self) -> $name {
        $name(self)
      }
    }
    impl $name {
      pub fn inner(&self) -> &$inner {
        &self.0
      }
      pub fn inner_mut(&mut self) -> &mut $inner {
        &mut self.0
      }
    }
  };
}

pub fn new_tmp_idx() -> String {
  thread_local! {
    static COUNTER: std::cell::RefCell<usize> = std::cell::RefCell::new(0);
  }
  COUNTER.with(|c| {
    let mut counter = c.borrow_mut();
    *counter += 1;
    format!("tmp{}", *counter)
  })
}
