/-!
V7 Independence of F from B0.
-/

namespace IDT
namespace QMClosure

def Ctx := Bool
def Alt := Bool

def R : Ctx → Alt → Prop
  | false, false => False
  | false, true  => True
  | true,  _     => True

def D (_c : Ctx) (_a _b : Alt) : Prop := True

theorem b0Satisfied : (∀ c a, R c a ∨ ¬ R c a) ∧ (∀ c a b, D c a b) := by
  constructor
  · intro c a
    match c, a with
    | false, false => exact Or.inr id
    | false, true  => exact Or.inl trivial
    | true,  _     => exact Or.inl trivial
  · intro c a b; exact trivial

def F : Prop := ∀ (c1 c2 : Ctx) (a : Alt), R c2 a → R c1 a

-- F fails because h false true false : R true false → R false false
-- = True → False
theorem Ffails : ¬ F := by
  intro h
  have h1 := h false true false
  -- h1 : True → False
  exact h1 trivial

theorem b0WithoutF : (∀ c a b, D c a b) ∧ ¬ F :=
  ⟨fun _ _ _ => trivial, Ffails⟩

def status : String := "proved"

end QMClosure
end IDT
