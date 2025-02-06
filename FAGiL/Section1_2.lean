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


instance: CategoryTheory.Limits.IsInitial (RingCat.of ℤ) :=
  CategoryTheory.Limits.IsInitial.ofUnique (RingCat.of ℤ)

end section
