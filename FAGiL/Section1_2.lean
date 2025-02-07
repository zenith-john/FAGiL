/-
Copyright (c) 2025 Nantao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Nantao Zhang
-/

import FAGiL.Section1_1
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic
import Mathlib.Topology.Category.TopCat.Basic

open CategoryTheory
/-
(1.2.2)
The initial, final are defined in Mathlib.CategoryTheory.Limits.Shapes.isTerminal.
And zero objects are defined in Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects.
IsInitial (resp. IsTerminal, isZero) X is a proposition that X is an initial
(resp. final, zero) object in category C. The definition is given as limit (resp. colimit,
limit and colimit) of empty diagram.

The definition Category.Theory.Limits.IsInitial.ofUnique (resp. IsTerminal.ofUnique) shows
that definition in the book induces definition in Mathlib.
-/

/-
(1.2.A)
See CategoryTheory.Limits.IsInitial.uniqueUpToIso (resp. IsTerminal.uniqueUpToIso) in
Mathlib.CategoryTheory.Limits.Shapes.IsTerminal.
-/

/-
(1.2.B) Show the initial and final object in Sets, Rings and Top.
-/

section
/-
TODO: Show emptyset is initial object in Set Category.
def emptySet := sorry
-/

-- Show that set with one object is final object.
instance : (X: Type) → Unique (X ⟶ Unit) := by
  intro X
  exact Pi.unique

instance : CategoryTheory.Limits.IsTerminal Unit :=
  CategoryTheory.Limits.IsTerminal.ofUnique Unit

end section

section
variable (R: RingCat)

-- Show that integer ring is initial object in RingCat.
instance : Unique (RingCat.of ℤ ⟶ R) :=
  {
    default :=
      RingCat.ofHom {
        toFun := λ n => n • (1 : R),
        map_zero' := by simp,
        map_add' := λ a b => by simp [add_smul],
        map_one' := by simp,
        map_mul' := λ a b => by simp [mul_smul]
      }
    uniq := by
      intro g
      ext x
      induction x using Int.induction_on with
      | hz => simp [g.hom.map_zero]
      | hp n ih => simp [g.hom.map_add, ih]
      | hn n ih => simp [g.hom.map_add, ih]
  }


instance : CategoryTheory.Limits.IsInitial (RingCat.of ℤ) :=
  CategoryTheory.Limits.IsInitial.ofUnique (RingCat.of ℤ)

-- Show that zero ring is final object in RingCat.
inductive zeroRing where
  | zero

instance : Ring zeroRing := {
  add := λ _ _ => zeroRing.zero,
  add_assoc := λ _ _ _ => rfl,
  zero := zeroRing.zero,
  zero_add := λ _ => rfl,
  add_zero := λ _ => rfl,
  nsmul := λ _ _ => zeroRing.zero,
  add_comm := λ _ _ => rfl,
  mul := λ _ _ => zeroRing.zero,
  left_distrib := λ _ _ _ => rfl,
  right_distrib := λ _ _ _ => rfl,
  zero_mul := λ _ => rfl,
  mul_zero := λ _ => rfl,
  mul_assoc := λ _ _ _ => rfl,
  one := zeroRing.zero,
  one_mul := λ _ => rfl,
  mul_one := λ _ => rfl,
  neg := λ _ => zeroRing.zero,
  zsmul := λ _ _ => zeroRing.zero,
  neg_add_cancel := λ _ => rfl
}

instance : Unique (R ⟶ RingCat.of zeroRing) :=
  {
    default :=
      RingCat.ofHom {
        toFun := λ n => zeroRing.zero,
        map_zero' := by simp,
        map_add' := λ a b => by simp [add_smul],
        map_one' := by simp,
        map_mul' := λ a b => by simp [mul_smul]
      }
    uniq := by
      intro g
      ext x
      have hp: g.hom x = zeroRing.zero := rfl
      apply hp
  }

instance : CategoryTheory.Limits.IsTerminal (RingCat.of zeroRing) :=
  CategoryTheory.Limits.IsTerminal.ofUnique (RingCat.of zeroRing)

end section

section

variable (X: TopCat)

/-
TODO: Show empty space is initial object in Top Category.
def emptySet := sorry
-/

-- Show one point space is final object in Top Category.
inductive onePoint where
  | pt

instance : TopologicalSpace onePoint := {
  IsOpen := λ s => s = ∅ ∨ s = {onePoint.pt},
  isOpen_univ := by aesop
  isOpen_inter := by
    intros s t hs ht
    cases hs <;> cases ht <;>
    aesop,
  isOpen_sUnion := by
    intros S hS
    by_cases h : ∃ s ∈ S, s = {onePoint.pt}
    · aesop
    · have hq: ∀ s ∈ S, s = ∅ := by
        intro s hs
        by_cases hr: onePoint.pt ∈ s
        · exfalso
          apply h
          use s
          constructor; exact hs
          aesop
        · aesop
      have hp :⋃₀ S = ∅ := by exact Set.sUnion_eq_empty.mpr hq
      left
      exact hp
}

instance : Unique (X ⟶ TopCat.of onePoint) :=
  {
    default := {
      toFun := λ _ => onePoint.pt
    }

    uniq := by
      intro g
      ext x
      have hp: g x = onePoint.pt := rfl
      apply hp
  }

end section
