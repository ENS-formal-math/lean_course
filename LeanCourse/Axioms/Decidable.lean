namespace Hidden

-- Decidability is defined as --
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p

-- if c then t else e is a syntactic sugar for --
def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)

-- if h : c then t else e is a syntactic sugar for --
def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t

def eq_nat (a b : Nat) : Decidable (a = b) :=
  match a, b with
  | Nat.zero, Nat.zero => Decidable.isTrue (by rfl)
  | Nat.zero, Nat.succ b' => Decidable.isFalse (by exact Nat.zero_ne_add_one b')
  | Nat.succ a', Nat.zero => Decidable.isFalse (by exact Nat.add_one_ne_zero a')
  | Nat.succ a', Nat.succ b' =>
    match eq_nat a' b' with
    | Decidable.isFalse h => Decidable.isFalse (by intro hneq; exact h (Nat.succ_inj'.mp hneq))
    | Decidable.isTrue h => Decidable.isTrue (by exact congrArg Nat.succ h)

instance {a b : Nat} : Decidable (a = b) := eq_nat a b

#eval 3 = 3

end Hidden

def decidable_eq_nat (a b : ℕ) [h : Decidable (a = b)] :=
  match h with
  | Decidable.isFalse _ => 0
  | Decidable.isTrue _ => 1

def decidable_if (c : Prop) [h: Decidable c] (t e : α) : α :=
  match h with
  | Decidable.isFalse _ => e
  | Decidable.isTrue _ => t

#eval decidable_eq_nat 3 3

#eval decidable_if (2 = 3) 1 0
