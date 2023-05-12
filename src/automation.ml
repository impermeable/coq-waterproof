let test (id: Names.Id.t) : unit Proofview.tactic =
  Feedback.msg_notice (Ppconstr.pr_id id);
  Auto.auto ~debug:Off 0 [] []