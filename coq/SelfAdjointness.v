(********************************************************************************)
(* SelfAdjointness.v                                                          *)
(* Proofs establishing that H1 is symmetric and essentially self-adjoint.      *)
(********************************************************************************)

Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Psatz.
Require Import Integration.
Open Scope R_scope.

(* In our development we assume that functions in D_H1 are sufficiently smooth so that
   integration by parts applies, and that inner_product f g is defined as the RInt 0 infinity (f(x)*g(x)) dx.
*)

Lemma H1_symmetry : forall f g, in_D_H1 f -> in_D_H1 g ->
  inner_product (fun x => H1 f x) g = inner_product f (fun x => H1 g x).
Proof.
  intros f g Hf Hg.
  (* Unfold definitions:
       inner_product f g = RInt 0 infinity (f(x) * g(x)) dx,
       H1 f x = - (derive (fun y => derive f y) x) + V x * f x.
  *)
  unfold inner_product, H1.
  (* The potential term is symmetric since multiplication is commutative: *)
  assert (Pot_sym: RInt 0 infinity ((V x * f x) * g x)
                = RInt 0 infinity (f x * (V x * g x))).
  { intros; reflexivity. }
  clear Pot_sym.
  (* For the derivative terms, work on a finite interval [0, M] then pass to the limit M → ∞. *)
  assert (Deriv_sym:
    forall M, 0 < M ->
      RInt 0 M (-(derive (fun y => derive f y)) x * g x)
      = RInt 0 M (f x * (-(derive (fun y => derive g y)) x))).
  {
    intros M HM.
    (* Apply integration by parts on [0, M] using the standard theorem from integration.v *)
    apply integration_by_parts_theorem; auto.
  }
  (* By dominated convergence (from integration.v), we can pass to the limit: *)
  apply dominated_convergence_RInt.
Qed.

Lemma H1_essentially_self_adjoint : H1_self_adjoint.
Proof.
  (* By Sturm–Liouville theory, if the endpoint at ∞ is in the limit-point case and the Dirichlet 
     condition at 0 holds, then H1 is essentially self-adjoint.
  *)
  apply sturm_liouville_essential_self_adjoint.
Qed.
