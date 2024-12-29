/-
Copyright (c) 2024 Nantao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Nantao Zhang
-/
import Mathlib.Tactic


universe u u₁ v

open CategoryTheory
open Function

section

variable {C: Type u} [Category.{v} C] {X Y Z: C}
variable {α: Type u₁}
/-
(1.1.1) The category is defined by Mathlib.CategoryTheory.Category.Basic.Category
-/

/-
(1.1.2) Set is a category.
-/
instance : Category (Set α) where
  Hom X Y := X → Y
  id X := id
  comp f g := fun a ↦ g (f a)

/-
(1.1.3) Vect_k is a category.
-/


/-
(1.1.A) The groupoid is defined by Mathlib.CategoryTheory.Groupoid.Groupoid
-/

/-
(1.1.B) The invertible morphism is defined by Mathlib.CategoryTheory.Iso.Iso
The proof is copied from Mathlib.CategoryTheory.Endomorphism
-/
instance : Group (X ≅ X) where
  one := Iso.refl X
  inv := Iso.symm
  mul x y := Iso.trans y x
  mul_assoc _ _ _ := (Iso.trans_assoc _ _ _).symm
  one_mul := Iso.trans_refl
  mul_one := Iso.refl_trans
  inv_mul_cancel := Iso.self_symm_id

end section
