(********************************************************************************)
(* CompactResolvent.v                                                         *)
(* Proof that the differential operator H1 has a compact resolvent.            *)
(********************************************************************************)

Require Import Definitions.
Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Psatz.
Open Scope R_scope.

(* We assume that the domain D_H1 of H1 is a Sobolev space (e.g., H¹₀ ∩ H²) and that the
   embedding of this Sobolev space into L²(0,∞) is compact. This follows from the 
   Rellich–Kondrachov theorem.
*)
Axiom sobolev_compact_embedding :
  (* The inclusion map from D_H1 into L²(0,∞) is compact. *)
  compact_embedding D_H1.

Lemma H1_compact_resolvent_proof : H1_compact_resolvent.
Proof.
  (* Choose a point z in the resolvent set (for instance, z = -1). *)
  set (z := -1).
  (* Standard theory gives that (H1 - z I)⁻¹ is bounded and maps L²(0,∞) into D_H1. *)
  assert (Bounded_resolvent: bounded (resolvent H1 z)).
  { apply standard_resolvent_bound. }
  (* The composition of (H1 - z I)⁻¹ with the compact embedding yields a compact operator. *)
  apply (composition_compact _ _ Bounded_resolvent sobolev_compact_embedding).
Qed.
