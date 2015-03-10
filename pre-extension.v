Require Export Foundations.hlevel2.hSet.
Require Export carrier.

About hfp.
              
Definition preextensionAlg ( x : ecarrier ) : UU :=
  total2
    ( fun e0 : eF x -> eC x =>
        ( total2 
            ( fun e1 : hfp e0 (eft x) -> eF x =>
                forall ( P : hfp e0 (eft x) ), eft x (e1 P) = eft x (pr1 (pr1 P))
            )
        )
    ).

Definition ectxext { x : ecarrier } ( CFT : preextensionAlg x ) : eF x -> eC x :=
  pr1 CFT.

Definition eF2 { x : ecarrier } ( CFT : preextensionAlg x ) : UU :=
  hfp (ectxext CFT) (eft x).

Definition efamext { x : ecarrier } ( CFT : preextensionAlg x ) : eF2 CFT -> eF x :=
  pr1 (pr2 CFT).

Definition eft2 { x : ecarrier } ( CFT : preextensionAlg x ) : eF2 CFT -> eF x :=
  fun AP => pr1 (pr1 AP).

Definition eF3 { x : ecarrier } ( CFT : preextensionAlg x ) : UU :=
  hfp (efamext CFT) (eft2 CFT). 

Definition eft3 { x : ecarrier } ( CFT : preextensionAlg x ) : eF3 CFT -> eF2 CFT :=
  fun APQ => pr1 (pr1 APQ).

Print total2.
Print dirprod.
Print pr1hSet.
Print hfp.

About paths.

Definition emixpr2 { x : ecarrier } ( CFT : preextensionAlg x ) (APQ : eF3 CFT) : eF2 CFT.
  Proof.
    destruct APQ as [[[[A P] s0] [[AP Q] s1]] s2].
    apply ( tpair
              ( fun xx' : dirprod (eF x) (eF x) =>
                  eft x (pr2 xx') = ectxext CFT (pr1 xx'))
              ( tpair (fun _ => eF x) P Q )
          ).
    simpl.
    simpl in s0. simpl in s1. unfold eft2 in s2. simpl in s2.
    rewrite s1.
    rewrite s2.

(*
Definition eext2 {CFT : ecarrier } ( CFTee : preextensionAlg CFT ) : eF3 CFTee -> eF2 CFTee :=
  fun APQ =>
    tpair (pr2 (pr1 (pr1 APQ))) (pr2 (pr2 (pr1 APQ))).

About hfp.
*)