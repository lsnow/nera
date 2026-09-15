//! Closed fixture shared by verifier, CLI and native tests.
use nera::SourceFile;
use nera::session::CompilerSession;
use nera::source::{SourceDatabase, SourceInput};

pub const APP: &str = "module app; use ops::choose; use ops::set;
pub fn main()->u64 {
    let x=40; let y=2; let mut total=0; let mut values=[0,0]; let mut flags=[false];
    for i in 0usize..2usize {
        invariant i<=2usize;
        let r=choose<u64>(i==0usize,&x,&y);
        total=total+*r; set<u64,2>(&mut values[0..2],i,42);
        set<bool,1>(&mut flags[0..1],0usize,true);
    }
    if values[1]!=42 {return 99;} if flags[0] {return total;} return 99;
}";
pub const OPS: &str = "module ops;
pub fn choose<T>(flag:bool,a:&T,b:&T)->&T
requires readable(a,0..1); requires readable(b,0..1);
ensures readable(result,0..1); reads (); writes ();
{if flag {return a;} else {return b;}}
pub fn set<T,const N:usize>(p:&mut [T],i:usize,value:T)
requires len(p)==N; requires i<N;
requires writable(p,0usize..N);
{p[i]=value; return;}";

pub fn session(app: &str, ops: &str) -> CompilerSession {
    CompilerSession::modules(
        SourceDatabase::new(vec![
            SourceInput::new("app", SourceFile::from_text("app.nera", app)),
            SourceInput::new("ops", SourceFile::from_text("ops.nera", ops)),
        ])
        .unwrap(),
        Default::default(),
        "app::main",
    )
    .unwrap()
}

pub fn erase_invariants(source: &str) -> String {
    source
        .split_inclusive('\n')
        .map(|line| {
            if line.trim_start().starts_with("invariant ") {
                line.chars()
                    .map(|c| if c == '\n' { '\n' } else { ' ' })
                    .collect::<String>()
            } else {
                line.to_owned()
            }
        })
        .collect()
}
