Require Export Foundations.hlevel2.hSet.
Require Export carrier.
Require Export preextension.

Definition isExtAlg { x : ecarrier } ( CFT : preextensionAlg x ) : UU :=
  forall ( APQ : eF3 CFT ), 
    efamext CFT (eext2 CFT APQ) = efamext CFT (pr2 (pr1 APQ)).

Definition ExtAlg ( x : ecarrier ) := total2 (@isExtAlg x).