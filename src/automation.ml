open Ltac2_plugin

let test (id: Names.Id.t) : unit Proofview.tactic =
  Feedback.msg_notice (Ppconstr.pr_id id);
  Tac2tactics.auto Off None [] (Some [Names.Id.of_string "core"])