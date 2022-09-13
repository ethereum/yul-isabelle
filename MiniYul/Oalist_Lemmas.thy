theory Oalist_Lemmas
  imports Oalist
begin

lemma empty_get :
  "get empty k = None"
  by(transfer; auto)


end