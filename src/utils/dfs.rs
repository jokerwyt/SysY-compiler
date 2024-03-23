
pub trait Dfs: TreeId {
  fn pre_process(&self) -> Result<(), String> { Ok(()) }
  fn call_down(&self) -> Result<(), String> {
    for child in self.get_childrens() {
      child.dfs()?;
    }
    Ok(())
  }
  fn post_process(&self) -> Result<(), String> { Ok(()) }

  /// Basic implementation of dfs
  /// pre_process() -> call_down() -> post_process
  fn simple_dfs(&self) -> Result<(), String> {
    self.pre_process()?;
    self.call_down()?;
    self.post_process()
  }

  fn dfs(&self) -> Result<(), String>;
}


/// This should be implemented on the id, instead of the node itself.
pub trait TreeId: Sized {
  fn get_parent(&self) -> Option<Self> {todo!()}
  fn get_childrens(&self) -> Vec<Self>;
}