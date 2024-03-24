use std::cell::RefCell;
use std::collections::HashMap;
use uuid::Uuid;

pub struct Arena<T> {
    data: HashMap<Uuid, RefCell<T>>,
}

impl<T> Arena<T> {
    fn new() -> Self {
        Self {
            data: HashMap::new(),
        }
    }

    fn get(&self, uuid: Uuid) -> Option<std::cell::Ref<T>> {
        self.data.get(&uuid).map(|x| x.borrow())
    }

    fn get_mut(&self, uuid: Uuid) -> Option<std::cell::RefMut<T>> {
        self.data.get(&uuid).map(|x| x.borrow_mut())
    }
}