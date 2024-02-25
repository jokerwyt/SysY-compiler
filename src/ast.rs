#[derive(Debug)]
pub struct CompUnit {
    pub func_def: FuncDef,
}
  
#[derive(Debug)]
pub struct FuncDef {
    pub func_type: FuncType,
    pub ident: String,
    pub block: Block,
}

#[derive(Debug)]
pub enum  FuncType {
    Int = 0,
}

#[derive(Debug)]
pub struct Block {
    pub stmt: Stmt,
}

#[derive(Debug)]
pub struct Stmt {
    pub num: i32
}

#[derive(Debug)]
pub struct Ident {
    pub name: String,
}

