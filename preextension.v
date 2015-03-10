Require Export Foundations.hlevel2.hSet.
Require Export carrier.

About hfp.
              
Definition preextensionAlg ( x : ecarrier ) : UU :=
  total2
    ( fun e0 : eF x -> eC x =>
        ( total2 
            ( fun e1 : hfp e0 (eft x) -> eF x =>
                dirprod
                  ( forall ( P : hfp e0 (eft x) ), 
                      eft x (e1 P) = eft x (pr1 (pr1 P))
                  )
                  ( forall ( P : hfp e0 (eft x) ),
                      e0 (e1 P) = e0 (pr2 (pr1 P))
                  )
            )
        )
    ).

Definition preextensionAlg_construct ( x : ecarrier ) ( e0 : eF x -> eC x )
           ( e1 : hfp e0 (eft x) -> eF x ) 
           ( codeq : forall ( P : hfp e0 (eft x) ), eft x (e1 P) = eft x (pr1 (pr1 P)) )
           ( domeq : forall ( P : hfp e0 (eft x) ), e0 (e1 P) = e0 (pr2 (pr1 P)))
           : preextensionAlg x.
  Proof.
  refine (tpair _ _ _).
  exact e0.
  refine (tpair _ _ _).
  exact e1.
  refine (tpair _ _ _); intro P.
  exact (codeq P).
  exact (domeq P).
  Qed.

Definition ectxext { x : ecarrier } ( CFT : preextensionAlg x ) : eF x -> eC x :=
  pr1 CFT.

Definition eF2 { x : ecarrier } ( CFT : preextensionAlg x ) : UU :=
  hfp (ectxext CFT) (eft x).

Definition efamext { x : ecarrier } ( CFT : preextensionAlg x ) : eF2 CFT -> eF x :=
  pr1 (pr2 CFT).

Definition eft2 { x : ecarrier } ( CFT : preextensionAlg x ) : eF2 CFT -> eF x :=
  fun AP => pr1 (pr1 AP).

Definition eextcodeq { x : ecarrier } ( CFT : preextensionAlg x) ( P : eF2 CFT ) :
  eft x (efamext CFT P) = eft x (eft2 CFT P) :=
  (pr1 (pr2 (pr2 CFT))) P.
 
Definition eextdomeq { x : ecarrier } ( CFT : preextensionAlg x) ( P : eF2 CFT ) :
  ectxext CFT (efamext CFT P) = ectxext CFT (pr2 (pr1 (P))) :=
  (pr2 (pr2 (pr2 CFT))) P.

Definition eF3 { x : ecarrier } ( CFT : preextensionAlg x ) : UU :=
  hfp (efamext CFT) (eft2 CFT). 

Definition eft3 { x : ecarrier } ( CFT : preextensionAlg x ) : eF3 CFT -> eF2 CFT :=
  fun APQ => pr1 (pr1 APQ).

Definition emixpr2 { x : ecarrier } ( CFT : preextensionAlg x ) (APQ : eF3 CFT) : eF2 CFT.
  Proof.
    destruct APQ as [[[[A P] s0] [[AP Q] s1]] s2].
    refine (tpair _ _ _).
    refine (tpair _ _ _).
    exact P. exact Q.
    simpl in *.
    rewrite s1.
    unfold eft2 in s2. simpl in *.
    rewrite s2.
    refine (eextdomeq CFT _).
  Qed.

Definition eext2 { x : ecarrier } ( CFT : preextensionAlg x ) : eF3 CFT -> eF2 CFT.
  intros [[[[A P] s0] [[AP Q] s1]] s2].
  refine (tpair _ _ _).
  refine (tpair _ _ _).
  exact A.
  refine (efamext CFT _).
  refine (tpair _ _ _).
  refine (tpair _ _ _).
  exact P.
  exact Q.
  unfold eft2 in s2.
  simpl in *.
  rewrite s1.
  rewrite s2.
  refine (eextdomeq CFT _).
  unfold eft2 in *.
  simpl in *.
  rewrite (eextcodeq CFT _).
  unfold eft2. simpl.
  exact s0.
  Qed.