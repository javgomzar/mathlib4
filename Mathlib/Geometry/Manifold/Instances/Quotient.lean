/-
Copyright (c) 2025 Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz,
Juan José Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz, Juan José Madrigal
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Quotients of manifolds

This file contains results about quotients of manifolds by group actions.

## Main results

* `MulAction.instChartedSpaceQuotient`: a choice of charted space structure on the quotient of a
  charted space by a free, properly-discontinuous group action.

## TODO

* if `G` acts smoothly, the quotient is an `IsManifold I n` for a suitable `ModelWithCorners I`.
* if `G` acts smoothly, the projection map is smooth

## tags
smooth manifold, smooth action, quotient manifold
-/

public noncomputable section

variable {H M : Type*} [TopologicalSpace M] [TopologicalSpace H] [ChartedSpace H M]

namespace MulAction

variable {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M]

/-!
## Charted space structure on quotient by a group
-/

/-- The induced charted space structure on the quotient of a charted space by a free, properly
discontinuous group action. -/
@[expose, to_additive]
instance instChartedSpaceQuotient : ChartedSpace H (orbitRel.Quotient G M) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
    |>.isLocalHomeomorph.chartedSpace Quotient.mk_surjective

end MulAction

namespace IsSubmersion

open Manifold TopologicalSpace

universe u

variable {𝕜 E' : Type*} {E : Type u} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}

structure RegularWitness (R : Setoid M) where
  H' : Type*
  tH' : TopologicalSpace H'
  E' : Type*
  nE' : NormedAddCommGroup E'
  nsE' : NormedSpace 𝕜 E'
  I' : ModelWithCorners 𝕜 E' H'
  csQ : ChartedSpace H' (Quotient R)
  imQ : IsManifold I' n (Quotient R)
  smQ : IsSubmersion I I' n (Quotient.mk R)

class IsRegular (R : Setoid M) where
  reg := Nonempty (RegularWitness R)

instance godement (R : Setoid M) : IsRegular R ↔ IsClosed (graph R) := sorry

end IsSubmersion
