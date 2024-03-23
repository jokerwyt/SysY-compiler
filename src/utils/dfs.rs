
pub struct DfsVisitor<Fpre, Fpost, T: TreeId> {
  pre_process: Fpre,
  post_process: Fpost,
  phantom: std::marker::PhantomData<T>,
}

impl<Fpre, Fpost, T> DfsVisitor<Fpre, Fpost, T> 
where 
  Fpre: Fn(&T) -> Result<(), String>,
  Fpost: Fn(&T) -> Result<(), String>,
  T: TreeId
{
  pub fn new(pre_process: Fpre, post_process: Fpost) -> Self {
    Self {
      pre_process,
      post_process,
      phantom: std::marker::PhantomData,
    }
  }

  pub fn dfs(&self, node: &T) -> Result<(), String> {
    (self.pre_process)(node)?;
    for child in node.get_childrens() {
      self.dfs(&child)?;
    }
    (self.post_process)(node)?;
    Ok(())
  }
}

pub trait TreeId: Sized {
  fn get_parent(&self) -> Option<Self> {unimplemented!()}
  fn get_childrens(&self) -> Vec<Self>;
}