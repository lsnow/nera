use nera::{ValidatedVirUnit, VirOriginId, VirOriginKind};

pub fn runtime_with_resolved_origins(unit: &ValidatedVirUnit) -> String {
    // Spec can renumber origins. Compare complete payloads, not table indices.
    let dump = unit.runtime().stable_dump();
    let mut normalized = String::new();
    for (index, part) in dump.split("origin").enumerate() {
        if index == 0 {
            normalized.push_str(part);
            continue;
        }
        normalized.push_str("origin");
        let digits = part.bytes().take_while(u8::is_ascii_digit).count();
        if digits != 0 {
            let mut id = VirOriginId::new(part[..digits].parse().unwrap());
            loop {
                match &unit.as_unit().source_map.origin(id).unwrap().kind {
                    VirOriginKind::Generated { parent, reason } => {
                        normalized.push_str(&format!("[{reason:?}]"));
                        id = *parent;
                    }
                    user @ VirOriginKind::User { .. } => {
                        normalized.push_str(&format!("[{user:?}]"));
                        break;
                    }
                }
            }
        }
        normalized.push_str(&part[digits..]);
    }
    normalized
}
