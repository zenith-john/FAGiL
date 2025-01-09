/-
Copyright (c) 2024 Nantao Zhang, Hongyu Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Nantao Zhang
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open CategoryTheory
open Function

section
/-
(1.1.1) The category is defined by Mathlib.CategoryTheory.Category.Basic.Category
-/

/-
(1.1.2) Set is a category.
Remark: The set in mathematics is closer to [`Type`] in Lean4.
And the [`Set`] in mathlib4 is in fact closer to subset in mathematics.
-/

instance : Category Type where
  Hom X Y := X → Y
  id X := fun x => x
  comp f g := fun x => g (f x)
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

/-
(1.1.3) k vector space from a category.
-/
variable (R : Type*) [Ring R]
instance : Category (ModuleCat R) where
  Hom X Y := LinearMap (RingHom.id R) X Y
  id X := LinearMap.id
  comp f g := LinearMap.comp g f
  id_comp := by
    intros
    rfl
  comp_id := by
    intros
    rfl
  assoc := by
    intros
    rfl

/-
(1.1.A) The groupoid is defined by Mathlib.CategoryTheory.Groupoid.Groupoid
-/

/-
(1.1.B) The invertible morphism is defined by Mathlib.CategoryTheory.Iso.Iso
The proof is copied from Mathlib.CategoryTheory.Endomorphism
-/
variable {C: Type*} [Category C] {X: C}
instance : Group (X ≅ X) where
  one := Iso.refl X
  inv := Iso.symm
  mul x y := Iso.trans y x
  mul_assoc _ _ _ := (Iso.trans_assoc _ _ _).symm
  one_mul := Iso.trans_refl
  mul_one := Iso.refl_trans
  inv_mul_cancel := Iso.self_symm_id

/-
(1.1.4) Abelain groups form a category.
Defined as Mathlib.Algebra.Category.Grp.Basic.AddCommGrp
-/


/-
(1.1.5) Module over a ring form a category.
See (1.1.3).
-/

/-
(1.1.6) Rings from a category.
Defined as Mathlib.Algebra.Category.Ring.Basic.RingCat
-/

/-
(1.1.7) Topological spaces form a category.
See TopCat in Mathlib.Topology.Category.TopCat.Basic.lean
-/

/-
(1.1.8) Partially ordered set is a category.
-/
variable (α: Type*) [PartialOrder α]

instance : Unique Unit where
  uniq := by
    intro a
    rfl

@[ext]
structure POHom (X: α) (Y: α) where
  mk ::
  unit: Unit
  p: X ≤ Y

lemma POHom_eq (X Y : α) (a b: POHom α X Y) : a = b := by
  ext


instance : Category α where
  Hom X Y := POHom α X Y
  id X := POHom.mk () (le_refl X)
  comp f g := POHom.mk () (le_trans f.p g.p)
  id_comp := by intros; apply POHom_eq
  comp_id := by intros; apply POHom_eq
  assoc := by intros; apply POHom_eq

/-
(1.1.9.a) Subsets of a set with morphisms inclusion maps form a category.
-/
variable {β: Type*}
instance : PartialOrder (Set β) where
  le := (· ⊆ ·)
  le_refl := Set.Subset.refl
  le_trans := by
    intros _ _ _ p q
    exact Set.Subset.trans p q
  le_antisymm := fun a b h₁ h₂ => Set.Subset.antisymm h₁ h₂

instance : Category (Set β) where

/-
(1.1.9.b) Open subsets of a topological space form a category.
-/
variable (γ: Type*) [TopologicalSpace γ]

@[ext]
structure OpenSubset where
  mk ::
  set : Set γ
  is_open : IsOpen set

instance : PartialOrder (OpenSubset γ) where
  le a b := (a.set ⊆ b.set)
  le_refl := by intros; exact fun ⦃a⦄ a ↦ a
  le_trans := by
    intros _ _ _ hab hbc
    exact Set.Subset.trans hab hbc
  le_antisymm := by
    intros _ _ hab hba
    apply OpenSubset.ext
    exact Set.Subset.antisymm hab hba

instance : Category (OpenSubset γ) where

end section
