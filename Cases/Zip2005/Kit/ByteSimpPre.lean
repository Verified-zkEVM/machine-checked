import Lean

/-! The `byte_pre` set: `byte_simp`'s rewrites applied top-down (`↓`), for cells whose terms nest
dead contents (a frame buffer reused by consecutive reads): the outer constructors are taken apart
first and the inner contents dropped without being visited. -/

register_simp_attr byte_pre
