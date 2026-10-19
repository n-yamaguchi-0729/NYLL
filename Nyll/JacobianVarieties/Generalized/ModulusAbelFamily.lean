/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedDivisor
import Nyll.JacobianVarieties.Generalized.PicardSheaf
import Nyll.AlgebraicCurves.RelativeDivisors.Support.SupportedInOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.LineBundles.InvertibleI

/-!
# The actual modulus-rigidified Abel family

On the complement of the full closed modulus, the graph of the moving point is
an effective relative divisor of degree one. Its inverse ideal has its canonical
section, which is nowhere zero on the base-changed modulus. Sending this section
to one gives a specific rigidification, including along nonreduced moduli.

The resulting family defines an actual natural transformation from the open
curve's functor of points to the fppf modulus Picard sheaf. Its factorization
through a represented degree-one torsor is a separate construction.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]

/-- The open complement of the scheme-theoretic modulus. -/
def modulusComplement : C.Opens := i.ker.support.compl

/-- No point of the modulus belongs to its open complement. -/
theorem modulus_not_mem_complement (y : D) :
    i y ∉ modulusComplement i := by
  change i y ∉ i.ker.support.compl
  intro hy
  have hs : i y ∈ (i.ker.support : Set C) := by
    rw [Scheme.Hom.support_ker]
    exact subset_closure ⟨y, rfl⟩
  exact hy hs

variable [IsSeparated c] [SmoothOfRelativeDimension 1 c]

/-- The actual moving graph over the complement is a relative divisor of degree one. -/
def modulusAbelDivisor :
    RelEffCartierDiv c 1 ((modulusComplement i).ι ≫ c) :=
  RelEffCartierDiv.ofPoint c (modulusComplement i).ι rfl

omit [SmoothOfRelativeDimension 1 c] in
/-- The moving graph avoids the entire base-changed modulus. -/
theorem modulusAbelDivisor_avoids (y : (pullback (i ≫ c)
    ((modulusComplement i).ι ≫ c) : Scheme.{u})) :
    modulusBaseChange c i ((modulusComplement i).ι ≫ c) y ∉
      (modulusAbelDivisor c i).I.support := by
  intro hy
  have hs := RelEffCartierDiv.supportedIn_ofPoint
    (f := c) (modulusComplement i).ι rfl (modulusComplement i)
    (fun x => x.property)
  have hz := hs hy
  change pullback.fst c ((modulusComplement i).ι ≫ c)
    (modulusBaseChange c i ((modulusComplement i).ι ≫ c) y) ∈
      modulusComplement i at hz
  have hf : modulusBaseChange c i ((modulusComplement i).ι ≫ c) ≫
      pullback.fst c ((modulusComplement i).ι ≫ c) =
      pullback.fst (i ≫ c) ((modulusComplement i).ι ≫ c) ≫ i := by
    simp only [modulusBaseChange, pullback.map, pullback.lift_fst]
  rw [← Scheme.Hom.comp_apply, hf, Scheme.Hom.comp_apply] at hz
  exact modulus_not_mem_complement i _ hz

/-- `O(Δ)` with its canonical section normalized to one on the whole modulus. -/
def modulusAbelBundle :
    RigidifiedLineBundle
      (modulusBaseChange c i ((modulusComplement i).ι ≫ c)) :=
  RigidifiedLineBundle.ofInvertibleIdeal
    (modulusBaseChange c i ((modulusComplement i).ι ≫ c))
    (modulusAbelDivisor c i).I
    (RelEffCartierDiv.isInvertible_I (modulusAbelDivisor c i))
    (modulusAbelDivisor_avoids c i)

/-- The underlying line bundle is the inverse ideal of the actual degree-one graph. -/
theorem modulusAbelBundle_lineBundle :
    (modulusAbelBundle c i).L = (modulusAbelDivisor c i).I.invModule := rfl

/-- The chosen Abel rigidification sends the actual divisor section to one. -/
@[reassoc] theorem modulusAbelBundle_section :
    Scheme.Modules.pullbackSection
      (modulusBaseChange c i ((modulusComplement i).ι ≫ c))
      (modulusAbelDivisor c i).I.invModuleSection ≫
      (modulusAbelBundle c i).trivialization.hom =
        𝟙 (𝟙_ (pullback (i ≫ c) ((modulusComplement i).ι ≫ c)).Modules) :=
  RigidifiedLineBundle.ofInvertibleIdeal_section _ _ _ _

/-- The class of the actual diagonal line bundle with its canonical rigidification. -/
def modulusAbelClass : (modulusPicardPresheaf c i).obj
    (op (Over.mk ((modulusComplement i).ι ≫ c))) :=
  RigidifiedLineBundle.classOf (modulusAbelBundle c i)

/-- Pulling back the constructed global Abel family gives a natural map on all tests. -/
def modulusAbelPresheafMap :
    uliftYoneda.{u + 1}.obj (Over.mk ((modulusComplement i).ι ≫ c)) ⟶ modulusPicardPresheaf c i :=
  uliftYonedaEquiv.{u + 1}.symm (modulusAbelClass c i)

/-- The regular Abel family gives a map into the actual fppf Picard sheaf. -/
def modulusAbelSheafMap :
    uliftYoneda.{u + 1}.obj (Over.mk ((modulusComplement i).ι ≫ c)) ⟶
      (modulusPicardSheaf c i).obj :=
  modulusAbelPresheafMap c i ≫ toModulusPicardSheaf c i

/-- On any test scheme the Abel class is the actual pulled-back diagonal class. -/
theorem modulusAbelPresheafMap_apply
    (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    (modulusAbelPresheafMap c i).app (op T) (ULift.up x) =
      (modulusPicardPresheaf c i).map x.op (modulusAbelClass c i) :=
  rfl

/-- Sheafification retains the same constructed class on every test scheme. -/
theorem modulusAbelSheafMap_apply
    (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    (modulusAbelSheafMap c i).app (op T) (ULift.up x) =
      (toModulusPicardSheaf c i).app (op T)
        ((modulusPicardPresheaf c i).map x.op (modulusAbelClass c i)) := rfl

end AlgebraicGeometry.GeneralizedJacobian
