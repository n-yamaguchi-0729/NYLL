/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The original strictly-standard presentation under coefficient base change

Coefficient mapping preserves the actual Jacobian minors and both original
relation-ideal memberships. The quotient map is the native induced map of
the polynomial presentations. An original map into an algebra tower extends
to the changed presentation, with its original composite retained.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace MvPolynomial

variable {R S L m n k : Type*} [CommRing R] [CommRing S] [CommRing L]

/-- The relation ideal after coefficient mapping is the actual image of
the original relation ideal. -/
theorem map_relationIdeal (θ : R →+* S) (f : m → MvPolynomial n R) :
    Ideal.map (map θ) (Ideal.span (Set.range f)) =
      Ideal.span (Set.range fun j => map θ (f j)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-- Coefficient mapping carries each specified original Jacobian minor
to the same minor of the mapped relations. -/
theorem map_jacobianMinor [Fintype m] [DecidableEq m]
    (θ : R →+* S) (f : m → MvPolynomial n R) (c : m → n) :
    map θ (((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det) =
      ((Matrix.of fun j i => pderiv i (map θ (f j))).submatrix _root_.id c).det := by
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact pderiv_map.symm

/-- The ideal of the specified maximal Jacobian minors is preserved by
the actual coefficient map. -/
theorem map_jacobianMinorIdeal [Fintype m] [DecidableEq m]
    (θ : R →+* S) (f : m → MvPolynomial n R) :
    Ideal.map (map θ) (Ideal.span (Set.range fun c : m → n =>
        ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det)) =
      Ideal.span (Set.range fun c : m → n =>
        ((Matrix.of fun j i => pderiv i (map θ (f j))).submatrix _root_.id c).det) := by
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext c
  exact map_jacobianMinor θ f c

/-- The original polynomial strictly-standard data survive every actual
coefficient map, including the original residual-ideal conditions. -/
theorem strictStandard_data_map [Fintype m] [DecidableEq m]
    (θ : R →+* S) (p : MvPolynomial n R)
    (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (hminor : p ∈ (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ⊔
      Ideal.span (Set.range fun c : m → n =>
        ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det))
    (hrelations : ∀ j, p * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2) :
    map θ p ∈
        (Ideal.span (Set.range fun j => map θ (f j)) ⊔
          Ideal.span (Set.range fun j => map θ (h j))) ⊔
        Ideal.span (Set.range fun c : m → n =>
          ((Matrix.of fun j i => pderiv i (map θ (f j))).submatrix _root_.id c).det) ∧
      ∀ j, map θ p * map θ (h j) ∈
        Ideal.span (Set.range fun j => map θ (f j)) ⊔
          (Ideal.span (Set.range fun j => map θ (f j)) ⊔
            Ideal.span (Set.range fun j => map θ (h j))) ^ 2 := by
  constructor
  · have hp := Ideal.mem_map_of_mem (map θ) hminor
    rw [Ideal.map_sup, Ideal.map_sup, map_jacobianMinorIdeal θ f,
      map_relationIdeal, map_relationIdeal] at hp
    exact hp
  · intro j
    have hj := Ideal.mem_map_of_mem (map θ) (hrelations j)
    simpa only [Ideal.map_sup, Ideal.map_pow, map_relationIdeal, map_mul] using hj

section Algebra

variable [Algebra R S]

/-- The original polynomial quotient maps to its coefficient extension
by the native quotient map of the actual coefficient homomorphism. -/
def relationBaseChangeMap (f : m → MvPolynomial n R) (h : k → MvPolynomial n R) :
    (MvPolynomial n R ⧸ (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R]
      (MvPolynomial n S ⧸
        (Ideal.span (Set.range fun j => map (algebraMap R S) (f j)) ⊔
          Ideal.span (Set.range fun j => map (algebraMap R S) (h j)))) :=
  Ideal.quotientMapₐ _ (mapAlgHom (Algebra.ofId R S)) (by
    apply Ideal.map_le_iff_le_comap.mp
    change Ideal.map (map (algebraMap R S))
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ≤ _
    apply le_of_eq
    rw [Ideal.map_sup, map_relationIdeal, map_relationIdeal])

/-- The quotient coefficient map retains every actual polynomial. -/
theorem relationBaseChangeMap_mk (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (p : MvPolynomial n R) :
    relationBaseChangeMap (S := S) f h
        (Ideal.Quotient.mk (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) p) =
      Ideal.Quotient.mk
        (Ideal.span (Set.range fun j => map (algebraMap R S) (f j)) ⊔
          Ideal.span (Set.range fun j => map (algebraMap R S) (h j)))
        (map (algebraMap R S) p) := rfl

/-- A base parameter retains both original strictly-standard memberships
after extension of its coefficients. -/
theorem strictStandard_data_baseChange [Fintype m] [DecidableEq m]
    (π : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (hminor : C π ∈ (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ⊔
      Ideal.span (Set.range fun c : m → n =>
        ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det))
    (hrelations : ∀ j, C π * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2) :
    C (algebraMap R S π) ∈
        (Ideal.span (Set.range fun j => map (algebraMap R S) (f j)) ⊔
          Ideal.span (Set.range fun j => map (algebraMap R S) (h j))) ⊔
        Ideal.span (Set.range fun c : m → n =>
          ((Matrix.of fun j i => pderiv i (map (algebraMap R S) (f j))).submatrix
            _root_.id c).det) ∧
      ∀ j, C (algebraMap R S π) * map (algebraMap R S) (h j) ∈
        Ideal.span (Set.range fun j => map (algebraMap R S) (f j)) ⊔
          (Ideal.span (Set.range fun j => map (algebraMap R S) (f j)) ⊔
            Ideal.span (Set.range fun j => map (algebraMap R S) (h j))) ^ 2 := by
  simpa only [map_C] using
    strictStandard_data_map (algebraMap R S) (C π) f h hminor hrelations

variable [Algebra R L] [Algebra S L] [IsScalarTower R S L]

/-- Scalar-linear maps from the changed presentation are determined by
their composite with the original quotient coefficient map. -/
theorem relationBaseChangeMap_hom_ext
    (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    {g₁ g₂ : (MvPolynomial n S ⧸
        (Ideal.span (Set.range fun j => map (algebraMap R S) (f j)) ⊔
          Ideal.span (Set.range fun j => map (algebraMap R S) (h j)))) →ₐ[S] L}
    (heq : (g₁.restrictScalars R).comp (relationBaseChangeMap (S := S) f h) =
      (g₂.restrictScalars R).comp (relationBaseChangeMap (S := S) f h)) :
    g₁ = g₂ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have hi := AlgHom.congr_fun heq
    (Ideal.Quotient.mk (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) (X i))
  change g₁ (Ideal.Quotient.mk _ (map (algebraMap R S) (X i))) =
    g₂ (Ideal.Quotient.mk _ (map (algebraMap R S) (X i))) at hi
  rw [map_X] at hi
  exact hi

/-- An original quotient map into a scalar tower extends to the actual
coefficient-changed presentation, with its original composite unchanged. -/
theorem exists_relationBaseChangeMap_lift
    (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (φ : (MvPolynomial n R ⧸
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] L) :
    ∃ φS : (MvPolynomial n S ⧸
        (Ideal.span (Set.range fun j => map (algebraMap R S) (f j)) ⊔
          Ideal.span (Set.range fun j => map (algebraMap R S) (h j)))) →ₐ[S] L,
      (φS.restrictScalars R).comp (relationBaseChangeMap (S := S) f h) = φ := by
  let I : Ideal (MvPolynomial n R) :=
    Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)
  let J : Ideal (MvPolynomial n S) :=
    Ideal.span (Set.range fun j => map (algebraMap R S) (f j)) ⊔
      Ideal.span (Set.range fun j => map (algebraMap R S) (h j))
  let q : MvPolynomial n R →ₐ[R] (MvPolynomial n R ⧸ I) := Ideal.Quotient.mkₐ R I
  let e : MvPolynomial n S →ₐ[S] L := aeval (fun i => φ (q (X i)))
  have he : (e.restrictScalars R).comp (mapAlgHom (Algebra.ofId R S)) = φ.comp q := by
    apply MvPolynomial.algHom_ext
    intro i
    change e (map (algebraMap R S) (X i)) = φ (q (X i))
    rw [map_X]
    exact aeval_X _ i
  have hzero (p : MvPolynomial n R) (hp : p ∈ I) : e (map (algebraMap R S) p) = 0 := by
    have hp' := AlgHom.congr_fun he p
    change e (map (algebraMap R S) p) = φ (q p) at hp'
    rw [show q p = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hp, _root_.map_zero] at hp'
    exact hp'
  have hker : J ≤ RingHom.ker e.toRingHom := by
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hzero (f j) ((show Ideal.span (Set.range f) ≤ I from le_sup_left)
        (Ideal.subset_span (Set.mem_range_self j)))
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hzero (h j) ((show Ideal.span (Set.range h) ≤ I from le_sup_right)
        (Ideal.subset_span (Set.mem_range_self j)))
  let φS : (MvPolynomial n S ⧸ J) →ₐ[S] L :=
    Ideal.Quotient.liftₐ J e (fun p hp => hker hp)
  refine ⟨φS, ?_⟩
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change e (map (algebraMap R S) p) = φ (q p)
  exact AlgHom.congr_fun he p

end Algebra

end MvPolynomial
