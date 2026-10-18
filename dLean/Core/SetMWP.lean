import Mathlib.Data.Set.Functor
import Std.WP
import Std.Tactic.Do

/-!
# SetMWP

The demonic weakest precondition for `SetM` requires the postcondition to hold
for every possible result. The `Std.WP` instances let `vcgen` reason about
nondeterministic programs using ordinary propositions as assertions.
-/

namespace dLean
open Std.WP Lean.Order

instance : WP (SetM α) α Prop EStack⟨⟩ where
  wpTrans xs := ⟨fun Q _ => ∀ a ∈ SetM.run xs, Q a⟩
  wp_trans_monotone _ := fun _ _ _ _ _ hQ h a ha => hQ a (h a ha)

instance : WPMonad SetM Prop EStack⟨⟩ where
  toWP _ := inferInstance
  pure_le_wp_pure a Q _ := by
    intro h x hx
    change x ∈ ({a} : Set _) at hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact h
  bind_le_wp_bind xs f Q _ := by
    intro h y hy
    change y ∈ ⋃ x ∈ SetM.run xs, SetM.run (f x) at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hx, hy⟩ := hy
    exact h x hx y hy

instance (xs : SetM α) : WPConjunctive xs where
  wp_meet_wp_le Q₁ Q₂ _ _ := by
    intro h a ha
    have h₁ := (meet_le_left _ _ : _ ⊑ wp xs Q₁ _) h
    have h₂ := (meet_le_right _ _ : _ ⊑ wp xs Q₂ _) h
    simpa only [meet_apply, meet_prop_eq_and] using And.intro (h₁ a ha) (h₂ a ha)

@[simp] theorem SetM.wp_pure (a : α) (Q : α → Prop) (E : EStack⟨⟩) :
    wp (pure a : SetM α) Q E = Q a := by
  apply propext
  change (∀ x ∈ ({a} : Set α), Q x) ↔ Q a
  simp

theorem SetM.wp_iff_run (p : SetM α) (Q : α → Prop) :
    wp p Q estack⟨⟩ ↔ (∀ x ∈ SetM.run p, Q x) := Iff.rfl

theorem SetM.of_wp_run_mem
    {p : SetM α} {res : α} (hres : res ∈ SetM.run p) (post : α → Prop)
    (hWP : wp p post estack⟨⟩) : post res := by
  exact hWP res hres

theorem SetM.wp_orElse
    (S S' : SetM α) {Q : α → Prop}
    (hxs : wp S Q estack⟨⟩) (hys : wp S' Q estack⟨⟩) :
    wp (S <|> S') Q estack⟨⟩ := by
  intro res hres
  rcases hres with hres | hres
  · exact hxs res hres
  · exact hys res hres

theorem SetM.wp_and (S : SetM α) {P Q : α → Prop}
    (hP : wp S P estack⟨⟩) (hQ : wp S Q estack⟨⟩) :
    wp S (fun a => P a ∧ Q a) estack⟨⟩ := by
  intro res hres
  exact ⟨hP res hres, hQ res hres⟩

end dLean
