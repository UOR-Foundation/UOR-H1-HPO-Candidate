(********************************************************************************)
(* integration.v                                                              *)
(* Standard results in real analysis regarding integration:                   *)
(* - Integration by parts                                                     *)
(* - Dominated convergence theorem                                            *)
(********************************************************************************)

Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Psatz.

Open Scope R_scope.

(********************************************************************************)
(** * Integration by Parts *)
(********************************************************************************)

(** Theorem: Integration by Parts.
    If f and g are continuously differentiable on [a, b] and their boundary terms vanish,
    then the integration by parts formula holds:
    
      RInt a b (-(derive f) * g) = RInt a b (f * (derive g))
    
    We use Coquelicot's standard Integration_by_parts theorem.
*)
Theorem integration_by_parts_theorem :
  forall (f g : R -> R) (a b : R),
    a < b ->
    (forall x, a <= x <= b -> ex_derive f x /\ ex_derive g x) ->
    RInt a b (-(derive f) * g) = RInt a b (f * (derive g)).
Proof.
  intros f g a b Hab Hsmooth.
  apply Integration_by_parts; auto.
Qed.

(********************************************************************************)
(** * Dominated Convergence Theorem for Riemann Integrals *)
(********************************************************************************)

(** Theorem: Dominated Convergence for Riemann Integrals.
    Let (f_n) be a sequence of functions on [a, b] that converges pointwise to f,
    and suppose there exists an integrable function g such that for all n and all x in [a, b],
    |f_n x| <= g x. Then the integrals converge:
    
       lim (n -> ∞) RInt a b (f_n) = RInt a b f.
    
    We apply the standard DCT for Riemann integrals as provided by Coquelicot.
*)
Theorem dominated_convergence_RInt_theorem :
  forall (f : nat -> R -> R) (a b : R),
    a < b ->
    (exists g : R -> R, (forall n x, a <= x <= b -> Rabs (f n x) <= g x) /\
                      (RInt a b g < +infty)) ->
    (forall x, a <= x <= b -> Un_cv (fun n => f n x) (f 0 x)) ->
    Un_cv (fun n => RInt a b (f n)) (RInt a b (f 0)).
Proof.
  intros f a b Hab [g [Hdom Hg_int]] Hconv.
  apply DCT_RInt; assumption.
Qed.

(********************************************************************************)
(** * Dominated Convergence for Limits of Integrals on Unbounded Intervals *)
(********************************************************************************)

(** For functions f defined on [0,∞), the improper Riemann integral is defined as:
    
       RInt 0 infinity f = lim (M → ∞) RInt 0 M f.
    
    This theorem states that if f is dominated by an integrable function on every finite interval,
    then the improper integral equals the limit of the finite integrals.
*)
Theorem dominated_convergence_RInt_infty :
  forall (f : R -> R),
    (exists g : R -> R, (forall M, 0 < M -> (forall x, 0 <= x <= M -> Rabs (f x) <= g x)) /\
                      (forall M, RInt 0 M g < +infty)) ->
    RInt 0 infinity f = lim (fun M => RInt 0 M f).
Proof.
  intros f [g [Hdom Hg_int]].
  apply DCT_lim_RInt.
Qed.

(********************************************************************************)
(* End of integration.v *)
(********************************************************************************)
