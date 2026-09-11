//! Shared stage 7.6.8 / 7.7.6 scale inputs; no verifier-derived expected answers.
pub const DIMENSIONS: [&str; 5] = ["chain", "scc", "alternatives", "aliases", "escaping"];
pub const SIZES: [usize; 4] = [1, 2, 4, 8];

pub fn source(dimension: &str, size: usize) -> String {
    match dimension {
        "chain" | "scc" => {
            let mut source = "fn main()->u64 { return f0(0); }".to_owned();
            for i in 0..size {
                let next = (i + 1) % size;
                let tail = if dimension == "chain" && i + 1 == size {
                    "return 42;".to_owned()
                } else {
                    format!("return f{next}(n+1);")
                };
                source.push_str(&format!(
                    "fn f{i}(n:u64)->u64 {{ if n=={size} {{ return 42; }} {tail} }}"
                ));
            }
            source
        }
        "alternatives" => {
            let mut source =
                "fn main()->u64 { return choose(0); } fn choose(n:u64)->u64 {".to_owned();
            for i in 0..size {
                source.push_str(&format!("if n=={i} {{ return {}; }}", 42 + i));
            }
            source.push_str("return 0; }");
            source
        }
        "escaping" => {
            let fields = (0..size)
                .map(|i| format!("p{i}:Own<u64>"))
                .collect::<Vec<_>>()
                .join(",");
            let init = (0..size)
                .map(|i| format!("let p{i}=alloc<u64>(1); *p{i}=42;"))
                .collect::<String>();
            let values = (0..size)
                .map(|i| format!("p{i}:p{i}"))
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "struct Bag {{ {fields}, }} fn main()->u64 {{ let b=make(); let p=b.p0; return *p; }} fn make()->Bag {{ {init} return Bag {{ {values} }}; }}"
            )
        }
        "aliases" => {
            let params = (0..size)
                .map(|i| format!("p{i}:&u64"))
                .collect::<Vec<_>>()
                .join(",");
            let args = vec!["&x"; size].join(",");
            let sum = (0..size)
                .map(|i| format!("*p{i}"))
                .collect::<Vec<_>>()
                .join("+");
            format!(
                "fn main()->u64 {{ let x=1; return read({args}); }} fn read({params})->u64 {{ return {sum}; }}"
            )
        }
        _ => panic!("unknown scale dimension: {dimension}"),
    }
}
