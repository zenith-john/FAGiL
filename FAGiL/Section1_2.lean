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

/- (1.2.1) Products defined by universal property are defined by Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts and
Mathlib.CategoryTheory.Limits.Shapes.Products, but defined as limits and colimits of some specific functors. -/

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
variable (X : Type)
-- Show that empty set is initial object in category of Sets.
instance : Unique (Empty ⟶ X) := {
  default := Empty.elim,
  uniq := by
    intro f
    ext X
    exact Empty.elim X
}
instance : CategoryTheory.Limits.IsInitial Empty :=
  CategoryTheory.Limits.IsInitial.ofUnique Empty

-- Show that set with one object is final object in category of Sets.
instance : Unique (X ⟶ Unit) := Pi.unique

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
        toFun := fun n => n • (1 : R),
        map_zero' := by simp,
        map_add' := fun a b => by simp [add_smul],
        map_one' := by simp,
        map_mul' := fun a b => by simp [mul_smul]
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
  add := fun _ _ => zeroRing.zero,
  add_assoc := fun _ _ _ => rfl,
  zero := zeroRing.zero,
  zero_add := fun _ => rfl,
  add_zero := fun _ => rfl,
  nsmul := fun _ _ => zeroRing.zero,
  add_comm := fun _ _ => rfl,
  mul := fun _ _ => zeroRing.zero,
  left_distrib := fun _ _ _ => rfl,
  right_distrib := fun _ _ _ => rfl,
  zero_mul := fun _ => rfl,
  mul_zero := fun _ => rfl,
  mul_assoc := fun _ _ _ => rfl,
  one := zeroRing.zero,
  one_mul := fun _ => rfl,
  mul_one := fun _ => rfl,
  neg := fun _ => zeroRing.zero,
  zsmul := fun _ _ => zeroRing.zero,
  neg_add_cancel := fun _ => rfl
}

instance : Unique (R ⟶ RingCat.of zeroRing) :=
  {
    default :=
      RingCat.ofHom {
        toFun := fun n => zeroRing.zero,
        map_zero' := by simp,
        map_add' := fun a b => by simp [add_smul],
        map_one' := by simp,
        map_mul' := fun a b => by simp [mul_smul]
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

-- Show empty space is initial object in Top Category.
instance : TopologicalSpace Empty := ⊥

instance : (X: TopCat) → Unique (TopCat.of Empty ⟶ X) := by
  intro X
  exact {
    default := {
      toFun := Empty.elim
    },
    uniq := by
      intro f
      ext x
      exact Empty.elim x
  }

instance : CategoryTheory.Limits.IsInitial (TopCat.of Empty) :=
  CategoryTheory.Limits.IsInitial.ofUnique (TopCat.of Empty)

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

/-
(1.2.3)
And the localization is defined as Localization/OreLocalization in Mathlib.GroupTheory.MonoidLocalization.Basic.
The multiplicative subset is a special case of submonoid. If view commutative ring as a commutative monoid and Ore
property is empty property. The ring strucutre of localized ring is given in Mathlib.RingTheory.OreLocalization.Basic.
-/

section

variable (R: Type*) [CommRing R] (S: Submonoid R)
example : CommRing R[S⁻¹] := inferInstance

end section

/-
(1.2.C) Show that S⁻¹A is injective if and only if S contains no zerodivisors.
-/

section

variable (A: Type*) [CommRing A] (S: Submonoid A)

theorem localization_map_injective_if_contains_no_zerodivisor :
  Function.Injective (algebraMap A A[S⁻¹]) ↔ S ≤ nonZeroDivisors A := by
    constructor
    · intros h s hs
      by_contra hns
      have hp : ∃ a ≠ 0, algebraMap A A[S⁻¹] a = 0 := by
        rw [nmem_nonZeroDivisors_iff] at hns
        choose a ha using hns
        use a
        rw [IsLocalization.map_eq_zero_iff S A[S⁻¹]]
        simp_all [ne_eq, Set.mem_setOf_eq, not_false_eq_true]
        use s
        rcases ha with ⟨ha1, ha2⟩
        constructor; exact hs; rw[← ha1]; ring
      have hq : algebraMap A A[S⁻¹] 0 = 0 := by exact algebraMap.coe_zero
      choose a ha using hp
      rcases ha with ⟨ha1, ha2⟩
      have hr: algebraMap A A[S⁻¹] 0 = algebraMap A A[S⁻¹] a := by rw[ha2, hq]
      apply h at hr
      apply ha1
      rw[hr]
    · intro hm
      exact IsLocalization.injective A[S⁻¹] hm

end section

/-
(1.2.D) Universial property of S⁻¹A.
-/

section

variable (A B: Type*) [CommRing A] [CommRing B] (S: Submonoid A) (f: A →+* B)

theorem universal_property_of_localization:
  (∀ s : S, IsUnit (f s)) → (∃! g : A[S⁻¹] →+* B, f = g ∘ (algebraMap A A[S⁻¹])) := by
  intro ha
  use IsLocalization.lift (M := S) (g := f) ha
  constructor
  · simp
    ext x
    have hp := IsLocalization.lift_eq (M := S) (g := f) ha (R := A) (S := A[S⁻¹])
    specialize hp x
    simp
  · intro h
    intro hq
    have hr : ∀ x : A, h ((algebraMap A A[S⁻¹]) x) = f x := by
      intro x
      rw[hq]
      simp
    have hs := IsLocalization.lift_unique ha hr
    rw[← hs]

end section

/-
(1.2.E)
Show existence of localization of modules defined by universal property. The definition of localization
of modules is given by quotient construction as LocalizedModule in Mathlib.Algebra.Module.LocalizedModule.Basic.
So it remains to show that that definition satisfies the universal property.
-/

section

variable (A M N) [CommRing A] (S: Submonoid A) [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N] (α: M →ₗ[A] N)

theorem univeral_property_of_localization_of_modules:
  (∀ s : S, IsUnit ((algebraMap A (Module.End A N)) s)) →
  (∃! g : LocalizedModule S M →ₗ[A] N, α = g ∘ₗ (LocalizedModule.mkLinearMap S M)) := by
  intro hs
  use LocalizedModule.lift S α hs
  constructor
  · simp
    rw[LocalizedModule.lift_comp S α hs]
  · intro g
    intro hp
    rw[LocalizedModule.lift_unique S α hs g hp.symm]

-- After writing above lines, I find the theorem in mathlib IsLocalizedModule.is_universal which do exactly the same thing.
end section

/-
(1.2.F)
TODO:
(a) Show that localization commutes with finite products.
(b) Show that localization commutes with arbitrary direct sums.
(c) Show that localization not necessarily commutes with arbitrary product.
-/

-- section

open DirectSum
universe u
variable (I A) [CommRing A] [Finite I] (S: Submonoid A)
variable (M: I → Type u) {m: (i: I) → AddCommMonoid (M i)} [(i: I) → Module A (M i)]

variable (C D)
def localization_commutes_with_finite_product:
  ((i:I) → (M i))[S⁻¹] ≃ₗ[A] ((i:I) → (M i)[S⁻¹]) := sorry

variable (J)
variable (N: J → Type u) {m: (j: J) → AddCommMonoid (N j)} [(j: J) → Module A (N j)]
def N' (j: J): Type u := (N j)[S⁻¹]

def localization_commutes_with_arbitrary_direct_sum:
  (⨁ j, N j)[S⁻¹] ≃ₗ[A] (⨁ j, (N j)[S⁻¹]) := sorry

-- end section

/-
(1.2.5)
Tensor product of modules is TensorProduct in Mathlib.LinearAlgebra.TensorProduct.Basic.
It can be written as M ⊗[R] N (after open namespace TensorProduct).
-/

/-
(1.2.G)
ℤ/(10) ⊗ ℤ/(12) ≅ ℤ/(2)
-/

variable {n: ℕ} (hn: 0 < n)
instance : Module ℤ (ZMod n) := inferInstance

def ZMod_map (n m: ℕ) (hn: (m ∣ n)): (ZMod n) →ₗ[ℤ] (ZMod m) := {
  toFun := ZMod.castHom (m := m) (n := n) hn (ZMod m),
  map_add' := by
    intros x y
    exact RingHom.map_add (ZMod.castHom hn (ZMod m)) x y
  map_smul' := by
    intros x y
    exact map_zsmul (ZMod.castHom hn (ZMod m)) x y
}

open scoped TensorProduct
example: (ZMod 10) ⊗[ℤ] (ZMod 12) ≃ₗ[ℤ] ZMod 2 := by sorry

variable (a b c: ℕ)
variable (n: ℕ)
instance: Module ℤ (ZMod n) := inferInstance

open TensorProduct
def tensorProductOfZMod (a b : ℕ) : ((ZMod a) ⊗[ℤ] (ZMod b) ≃ₗ[ℤ] (ZMod (Nat.gcd a b))) := by sorry


instance : (ZMod 10) ⊗[ℤ] (ZMod 12) ≃ₗ[ℤ] (ZMod 2) :=
  tensorProductOfZMod 10 12

/-
(1.2.H)
Tensor product is right exact.
See multiple theorems in Mathlib.LinearAlgebra.TensorProduct.RightExactness.
-/
