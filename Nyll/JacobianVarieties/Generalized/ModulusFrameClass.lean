/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusFrameTest
import Nyll.JacobianVarieties.Generalized.ParameterFrameClasses

/-!
# Intrinsic frame classes as actual modulus-rigidified bundles

On every parameter test scheme, the native scalar-frame quotient injects into
compatible-isomorphism classes on the actual curve family. Its image is exactly
the classes with underlying line bundle isomorphic to the pulled family.
Naturality across test schemes and sheaf-level Picard classification are separate.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual commuting inclusion square identifies the two parameter projections. -/
def modulusProjectionFrameClassesEquiv {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K))
    (M : (pullback (modulusBaseMap D) t).Modules) :
    ScalarFrameClasses (pullback.snd (modulusBaseMap D) t) M ≃
      ScalarFrameClasses (modulusFamilyInclusion D t ≫ pullback.snd c t) M :=
  Quotient.congr (Equiv.refl _) (fun e f => Iff.of_eq
    (congrArg (fun q : pullback (modulusBaseMap D) t ⟶ T => (scalarFrameSetoid q M).r e f)
      (modulusFamilyInclusion_snd D t)).symm)

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (L : (pullback c s).Modules)

/-- The native quotient agrees with the actual ambient-scalar quotient on a test scheme. -/
def modulusAmbientFrameEquiv (T : Over S) :
    (scalarFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T) ≃
        ScalarFrameClasses (modulusFamilyInclusion D (T.hom ≫ s))
          ((Scheme.Modules.pullback (modulusFamilyInclusion D (T.hom ≫ s))).obj
            ((Scheme.Modules.pullback
              (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))).obj L)) :=
  (modulusScalarFrameTestEquiv D s L T).trans
    ((modulusProjectionFrameClassesEquiv D (T.hom ≫ s) _).trans
      (curveParameterFrameClassesEquiv c (T.hom ≫ s)
        (modulusFamilyInclusion D (T.hom ≫ s)) _))

variable {L} (hL : Scheme.Modules.IsInvertible L)

/-- The intrinsic scalar-frame class gives a genuine modulus-rigidified bundle class. -/
def modulusFrameClass (T : Over S) :
    (scalarFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T) →
        RigidifiedLineBundle.Classes (modulusFamilyInclusion D (T.hom ≫ s)) :=
  RigidifiedLineBundle.frameClass (modulusFamilyInclusion D (T.hom ≫ s))
    (hL.pullback (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))) ∘
      modulusAmbientFrameEquiv D s L T

/-- Compatible rigidified isomorphisms create no extra identifications of native frame classes. -/
theorem modulusFrameClass_injective (T : Over S) :
    Function.Injective (modulusFrameClass D s hL T) :=
  (RigidifiedLineBundle.frameClass_injective (modulusFamilyInclusion D (T.hom ≫ s))
    (hL.pullback (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s)))).comp
      (modulusAmbientFrameEquiv D s L T).injective

/-- The image is exactly the genuine rigidifications of the pulled underlying family. -/
theorem exists_modulusFrameClass_eq_iff (T : Over S)
    (N : RigidifiedLineBundle (modulusFamilyInclusion D (T.hom ≫ s))) :
    (∃ x : (scalarFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T),
        modulusFrameClass D s hL T x = RigidifiedLineBundle.classOf N) ↔
          Nonempty (((Scheme.Modules.pullback
            (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))).obj L) ≅ N.L) := by
  let i := modulusFamilyInclusion D (T.hom ≫ s)
  let hM := hL.pullback (baseChangeSnd c (⟨T.hom, rfl⟩ : SchemeHomOver (T.hom ≫ s) s))
  constructor
  · rintro ⟨x, hx⟩
    exact (RigidifiedLineBundle.exists_frameClass_eq_iff i hM N).mp
      ⟨modulusAmbientFrameEquiv D s L T x, hx⟩
  · intro h
    obtain ⟨x, hx⟩ := (RigidifiedLineBundle.exists_frameClass_eq_iff i hM N).mpr h
    obtain ⟨y, hy⟩ := (modulusAmbientFrameEquiv D s L T).surjective x
    exact ⟨y, (congrArg (RigidifiedLineBundle.frameClass i hM) hy).trans hx⟩

end AlgebraicGeometry.GeneralizedJacobian
