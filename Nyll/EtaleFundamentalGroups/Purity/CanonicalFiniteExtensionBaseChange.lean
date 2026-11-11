/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.CanonicalFiniteExtension
import Nyll.SchemeTheory.Modules.Functoriality.RelativeSpecGlobalBaseChange

/-!
# Flat base change of the canonical finite extension

The original finite-etale cover is pulled back over the inverse image of
the given open. Its two direct-image algebras have their proved native
quasicoherence. The constructed relative-spectrum comparison therefore
gives the actual cartesian square, without a boundary-depth hypothesis
for the definition or an assumed algebra comparison.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace EtaleFundamentalGroups.FiniteBoundaryExtension

open AlgebraicGeometry

variable (X : Scheme.{u}) [IsLocallyNoetherian X]
  (U : X.Opens) {V : Scheme.{u}} (π : V ⟶ U.toScheme) [IsFinite π] [Etale π]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : Y ⟶ X)

omit [IsLocallyNoetherian X] [IsFinite π] [Etale π] [IsLocallyNoetherian Y] in
private theorem isPullback_openBaseChange :
    IsPullback (pullback.fst π (f ∣_ U))
      (pullback.snd π (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι) (π ≫ U.ι) f :=
  (IsPullback.of_hasPullback π (f ∣_ U)).paste_vert (isPullback_morphismRestrict f U)

/-- The comparison is built from the actual pulled-back finite-etale
cover and the original maps on sections. -/
def baseChangeMap :
    scheme Y (f ⁻¹ᵁ U) (pullback.snd π (f ∣_ U)) ⟶ scheme X U π := by
  have : (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent :=
    isQuasicoherent_underlyingModule X U π
  have : (Scheme.RelativeSpec.underlyingModule (Scheme.DirectImageAlgebra.structureMap
      (pullback.snd π (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι))).IsQuasicoherent :=
    isQuasicoherent_underlyingModule Y (f ⁻¹ᵁ U) (pullback.snd π (f ∣_ U))
  exact Scheme.DirectImageAlgebra.baseChangeMap (π ≫ U.ι)
    (pullback.snd π (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι) f (pullback.fst π (f ∣_ U))
    (isPullback_openBaseChange X U π f).w

/-- The canonical extension of the original pulled-back cover is the
actual flat pullback of the canonical extension. -/
theorem isPullback_baseChangeMap [Flat f] :
    IsPullback (baseChangeMap X U π f)
      (toBase Y (f ⁻¹ᵁ U) (pullback.snd π (f ∣_ U))) (toBase X U π) f := by
  have : (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent :=
    isQuasicoherent_underlyingModule X U π
  have : (Scheme.RelativeSpec.underlyingModule (Scheme.DirectImageAlgebra.structureMap
      (pullback.snd π (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι))).IsQuasicoherent :=
    isQuasicoherent_underlyingModule Y (f ⁻¹ᵁ U) (pullback.snd π (f ∣_ U))
  exact Scheme.DirectImageAlgebra.isPullback_baseChangeMap (π ≫ U.ι)
    (pullback.snd π (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι) f (pullback.fst π (f ∣_ U))
    (isPullback_openBaseChange X U π f)

/-- The actual isomorphism to the usual scheme-theoretic flat pullback. -/
def flatBaseChangeIso [Flat f] :
    scheme Y (f ⁻¹ᵁ U) (pullback.snd π (f ∣_ U)) ≅ pullback (toBase X U π) f :=
  (isPullback_baseChangeMap X U π f).isoPullback

@[reassoc]
theorem flatBaseChangeIso_hom_fst [Flat f] :
    (flatBaseChangeIso X U π f).hom ≫ pullback.fst (toBase X U π) f =
      baseChangeMap X U π f :=
  (isPullback_baseChangeMap X U π f).isoPullback_hom_fst

@[reassoc]
theorem flatBaseChangeIso_hom_snd [Flat f] :
    (flatBaseChangeIso X U π f).hom ≫ pullback.snd (toBase X U π) f =
      toBase Y (f ⁻¹ᵁ U) (pullback.snd π (f ∣_ U)) :=
  (isPullback_baseChangeMap X U π f).isoPullback_hom_snd

end EtaleFundamentalGroups.FiniteBoundaryExtension
