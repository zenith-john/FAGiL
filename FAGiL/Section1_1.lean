/-
Copyright (c) 2024 Nantao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Nantao Zhang, Hongyu Wang
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open CategoryTheory
open Function

section
/-
(1.1.1) The category is defined by Category in Mathlib.CategoryTheory.Category.Basic.
-/

/-
(1.1.2) Set is a category.
Remark: The set in mathematics is closer to `Type` in Lean4.
And the `Set` in mathlib4 is in fact closer to subset in mathematics.
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
(1.1.A) The groupoid is defined by Groupoid in Mathlib.CategoryTheory.Groupoid.
-/

/-
(1.1.B) The invertible morphism is defined by Iso in Mathlib.CategoryTheory.Iso.
The proof is copied from Mathlib.CategoryTheory.Endomorphism.
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
Defined as Mathlib.Algebra.Category.Grp.Basic.AddCommGrp.
-/

/-
(1.1.5) Module over a ring form a category.
See (1.1.3).
-/

/-
(1.1.6) Rings from a category.
Defined as RingCat in Mathlib.Algebra.Category.Ring.Basic.
-/

/-
(1.1.7) Topological spaces form a category.
Defined as TopCat in Mathlib.Topology.Category.TopCat.Basic.lean.
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

/-
(1.1.10) Definition of subcategory
Remark: The definition of subcategory here is a bit loose, as it allow to have Hom between
objects not in subcategory.
-/
structure Subcategory (C: Type*) [Category C] where
  carrier : Set C
  hom_carrier (X: C) (Y: C) : Set (X ⟶ Y)
  id_mem' {X} : X ∈ carrier → 𝟙 X ∈ hom_carrier X X
  comp_mem' {X Y Z} :
    X ∈ carrier → Y ∈ carrier → Z ∈ carrier →
    ∀ f ∈ hom_carrier X Y, ∀ g ∈ hom_carrier Y Z, f ≫ g ∈ hom_carrier X Z

/-
(1.1.11) Definition of (covariant) functor and identity functor.
Functor defined as CategoryTheory.Functor in Mathlib.CategoryTheory.Functor.Basic.
Identity functor defined as CategoryTheory.Functor.id in Mathlib.CategoryTheory.Functor.Basic.
The identify functor can be used as 𝟭(\sb1) C.
-/

section
variable (C: Type*) [Category C]
#check 𝟭 C
end section

/-
(1.1.12.a) Forget functor (to set) is the functor view underlying object as set and forget further
structures (abelian group, topological space, etc). The forget functor can be defined for concrete
category, and in mathlib, ConcreteCategory is a category with a forget functor.
See Mathlib/CategoryTheory/ConcreteCategory/Basic.lean.
-/

/-
(1.1.12.b) Forget functor from R-Mod to Ab is introduced in
ModuleCat.hasForgetToAddCommGroup in Mathlib.Algebra.Category.ModuleCat.Basic.
-/

/-
(1.1.13) Fundamental group is a functor.
TODO: The Mathlib has functor from `TopologicalSpace` to `Grpd`, but it require some additional work
to make it a functor from pointed space to groups.
-/

/-
(1.1.14) Hom(A, -) is a functor.
-/
section
universe u v
variable (C: Type u) [Category.{v} C] (X: C)
def homFunctor : C ⥤ Type v where
  obj Y := X ⟶ Y
  map f := fun g => g ≫ f

end section

/-
(1.1.15) Composition of functor is defined by
Functor.comp in Mathlib.CategoryTheory.Functor.Basic.
Can be used with notation ⋙.

Faithful functor is defined by
CategoryTheory.Functor.Faithful in Mathlib.CategoryTheory.Functor.FullyFaithful.

Full functor is defined by
CategoryTheory.Functor.Full in Mathlib.CategoryTheory.Functor.FullyFaithful.

Fully faithful functor is defined by
CategoryTheory.Functor.FullyFaithful in Mathlib.CategoryTheory.Functor.FullyFaithful.

Full subcategory is defined by
CategoryTheory.FullSubcategory in Mathlib.CategoryTheory.FullSubcategory.

Remark: Some examples about (not) full/faithful functor are omitted.
-/

/-
(1.1.16) Opposite category is defined by
CategoryTheory.Category.opposite in Mathlib.CategoryTheory.Opposites.
Contravariant functor from C to Dcan be defined as functor from Cᵒᵖ to D.
-/
def ContravariantFunctor (C D: Type*) [Category C] [Category D] := Functor Cᵒᵖ D

/-
(1.1.17) Taking dual is a ContravariantFunctor from Vect_k to Vect_k
-/
section

variable (k : Type*) [Field k]
instance dualVectorSpaceFunctor: ContravariantFunctor (ModuleCat k) (ModuleCat k) where
  obj X := ModuleCat.of k (Module.Dual k X.unop)
  map f := LinearMap.dualMap (Opposite.unop f)

end section

/-
(1.1.18) Cohomology functor H^i(X, ℤ) is a contravariant functor.
TODO: Cohomology seems not implemented in Mathlib.
-/

/-
(1.1.19) Mapping space to continuous functions on it is a contravariant functor.
Remark: This is indeed a special case of opHomFunctor. See (1.1.20).
-/


/-
(1.1.20) Hom(-, A) is a contravariant functor.
-/
section
universe u v
variable (C: Type u) [Category.{v} C] (X: Cᵒᵖ)
def opHomFunctor : ContravariantFunctor C (Type v) where
  obj Y := X ⟶ Y
  map f := fun g => g ≫ f

/- (* 1.1.19) -/
instance : TopologicalSpace ℝ := inferInstance
def continuousFunctionFunctor := opHomFunctor TopCat (Opposite.op (TopCat.of ℝ))
end section

/-
(1.1.21) Natural transformation is defined as
CategoryTheory.NatTrans in Mathlib.CategoryTheory.NatTrans.

Natural isomorphism in Mathlib is defined to be Iso in Functor.categroy.

Equivalence of categories is defined to be
CategoryTheory.Equivalence in Mathlib.CategoryTheory.Equivalence.
-/

/-
(1.1.C) The double dual of category of finite dimensional vector spaces is an equivalence.
-/
section
universe u v
-- class FinDimVectorSpace (k : Type*) (V : Type*) [Field k] [AddCommMonoid V] [AddCommGroup V] [Module k V] where
--   isFinDim: Module.Finite k V

variable (k: Type*) [Field k]
structure FinDimVectorSpaceCat where
  mk ::
  carrier: Type v
  [isAddCommGroup: AddCommGroup carrier]
  [isModule: Module k carrier]
  [isFinDim: FiniteDimensional k carrier]

variable (V : Type*) [AddCommGroup V] [Module k V]
-- Prove that the dual space is finite-dimensional
lemma of_dual : FiniteDimensional k V → FiniteDimensional k (Module.Dual k V) := by
  exact (Module.finite_dual_iff k).mpr


attribute [instance] FinDimVectorSpaceCat.isAddCommGroup FinDimVectorSpaceCat.isModule

instance : Category (FinDimVectorSpaceCat k) where
  Hom V W := V.carrier →ₗ[k] W.carrier
  id _ := LinearMap.id
  comp f g := g ∘ₗ f

instance doubleDualFunctor : FinDimVectorSpaceCat k ⥤ FinDimVectorSpaceCat k where
  obj X := {
    carrier := (Module.Dual k (Module.Dual k X.carrier)),
    isAddCommGroup := _,
    isModule := _,
    isFinDim := of_dual k (Module.Dual k X.carrier) (of_dual k X.carrier X.isFinDim),
  }
  map f := LinearMap.dualMap (LinearMap.dualMap f)
  map_id := by
    intros
    simp
    rfl
  map_comp := by
    intros X Y Z f g
    simp
    rfl

noncomputable
instance idToDoubleDual: NatTrans (𝟭 (FinDimVectorSpaceCat k)) (doubleDualFunctor k) where
  app X := by
    have p : Module.Free k X.carrier := by exact Module.Free.of_divisionRing k X.carrier
    have q : Module.Finite k X.carrier := by exact X.isFinDim
    simp
    exact (Module.evalEquiv k X.carrier).toLinearMap
  naturality f := by
    -- Generated by aesop?
    intro Y f_1
    simp_all only [Functor.id_obj, Functor.id_map, Module.evalEquiv_toLinearMap, id_eq]
    rfl

-- -- TODO: Fix this sorry.
-- noncomputable
-- instance doubleDualToId: NatTrans (doubleDualFunctor k) (𝟭 (FinDimVectorSpaceCat k)) where
--   app X := by
--     have p : Module.Free k X.carrier := by exact Module.Free.of_divisionRing k X.carrier
--     have q : Module.Finite k X.carrier := by exact X.isFinDim
--     simp
--     exact (Module.evalEquiv k X.carrier).symm.toLinearMap
--   naturality f := by

--     sorry

-- TODO: Show idToDoubleDual is Iso in Functor FinDimVectorSpaceCat k.


end section

/-
(1.1.D) The category of finite dimensional vector space with bases is equivalent to category of
finite dimensional vector spaces.
-/
section
variable (k: Type*) [Field k]

/-- A vector space with a chosen basis -/
structure VectorSpaceWithBasis where
  mk ::
  carrier: Type
  [isAddCommGroup: AddCommGroup carrier]
  [isModule: Module k carrier]
  [isFinDim: FiniteDimensional k carrier]
  basis: Basis (Fin (Module.finrank k carrier)) k carrier

attribute [instance] VectorSpaceWithBasis.isAddCommGroup VectorSpaceWithBasis.isModule

instance : Category (VectorSpaceWithBasis k) where
  Hom V W := V.carrier →ₗ[k] W.carrier
  id _ := LinearMap.id
  comp f g := g ∘ₗ f

/-- Forgetful functor that forgets the basis -/
def forgetBasis : VectorSpaceWithBasis k ⥤ FinDimVectorSpaceCat k where
  obj X := {
    carrier := X.carrier
    isAddCommGroup := X.isAddCommGroup
    isModule := X.isModule
    isFinDim := X.isFinDim
  }
  map f := f
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- Choose a basis-functor for a finite-dimensional vector space (using choice) -/
noncomputable def chooseBasis : FinDimVectorSpaceCat k ⥤ VectorSpaceWithBasis k where
  obj X := {
    carrier := X.carrier
    isAddCommGroup := X.isAddCommGroup
    isModule := X.isModule
    isFinDim := X.isFinDim
    basis := by
      have p : Module.Free k X.carrier := by exact Module.Free.of_divisionRing k X.carrier
      have q : Module.Finite k X.carrier := by exact X.isFinDim
      exact Module.finBasis k X.carrier
  }
  map f := f
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The forgetful functor and basis-choosing functor form an equivalence -/
noncomputable
instance vectorSpaceWithBasisEquiv : Equivalence (VectorSpaceWithBasis k) (FinDimVectorSpaceCat k) where
  functor := forgetBasis k
  inverse := chooseBasis k
  unitIso := NatIso.ofComponents
    (fun X => {
      hom := LinearMap.id
      inv := LinearMap.id
      hom_inv_id := rfl
      inv_hom_id := rfl
    })
    (by intros; rfl
      )
  counitIso := NatIso.ofComponents
    (fun X => {
      hom := LinearMap.id
      inv := LinearMap.id
      hom_inv_id :=  rfl
      inv_hom_id := rfl
    })
    (by intros; rfl)
end section

/-
(1.1.22) A functor is an equivlance of categories if and only if it is full faithful and essentially surjective.
The definition of CategoryTheory.Functor.IsEquivlance in Mathlib.CategoryTheory.Equivalence is a functor that is full,
faithful and essentially surjective.

LHS to RHS is CategoryTheory.Equivalence.isEquivalence_functor.
RHS to LHS is CategoryTheory.Functor.asEquivalence.
-/

end section
