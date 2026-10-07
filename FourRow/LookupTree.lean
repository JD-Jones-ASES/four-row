/-! Kernel-friendly logarithmic lookup for literal finite certificate tables.
Arrays reduce to lists in the kernel; this tree avoids repeated linear scans.
No lookup correctness axiom is needed: every concrete use is kernel checked.
-/
namespace FourRow

inductive LookupTree (α : Type u) where
  | leaf : α → LookupTree α
  | node : LookupTree α → LookupTree α → LookupTree α

namespace LookupTree

def get (t : LookupTree α) (i : Nat) : α :=
  match t with
  | leaf a => a
  | node left right => if i % 2 = 0 then left.get (i / 2) else right.get (i / 2)

end LookupTree
end FourRow
