//! Shared multi-module contract fixture for verifier and actual native consumers.
use nera::SourceFile;
use nera::session::CompilerSession;
use nera::source::{SourceDatabase, SourceInput};

pub const APP: &str = "module app; use left::run_left; use right::run_right;
    fn main()->u64 {return run_left()+run_right();}";
pub const LEFT: &str = "module left;
    pub fn run_left()->u64 {let mut a=[40,1]; let p=view<u64,2>(&mut a[0..2]);
        let x=p[0]; let y=p[1]; let mut flags=[true];
        let flag_view=view<bool,1>(&mut flags[0..1]); let flag=flag_view[0];
        let chosen=choose<u64>(flag,&x,&y); return *chosen+y;}
    fn view<T,const N:usize>(p:&mut [T])->&mut [T]
    requires len(p)==N; requires writable(p,0usize..N);
    ensures len(result)==N; ensures readable(result,0usize..N);
    reads (); writes ();
    {return p;}
    fn choose<T>(flag:bool,a:&T,b:&T)->&T
    requires readable(a,0..1); requires readable(b,0..1);
    ensures readable(result,0..1); reads (); writes ();
    {if flag {return a;} else {return b;}}";
pub const RIGHT: &str = "module right;
    pub fn run_right()->u64 {let mut a=[true]; let p=view<bool,1>(&mut a[0..1]);
        let value=p[0]; if value {return 1;} return 0;}
    fn view<T,const N:usize>(p:&mut [T])->&mut [T]
    requires len(p)==N; requires writable(p,0usize..N);
    ensures len(result)==N; ensures readable(result,0usize..N);
    reads (); writes ();
    {return p;}";

pub fn session(files: &[(&str, &str)]) -> CompilerSession {
    CompilerSession::modules(
        SourceDatabase::new(
            files
                .iter()
                .map(|(name, text)| {
                    SourceInput::new(*name, SourceFile::from_text(format!("{name}.nera"), text))
                })
                .collect(),
        )
        .unwrap(),
        Default::default(),
        "app::main",
    )
    .unwrap()
}
