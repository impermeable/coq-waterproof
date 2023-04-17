let _ = Mltop.add_known_module "coq-waterproof.plugin"

# 3 "src/g_waterproof.mlg"
 

open Ltac_plugin
open Pp
open Stdarg

open Automation



let () = Vernacextend.vernac_extend ~plugin:"coq-waterproof.plugin" ~command:"Hello" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("hello", 
                                     Vernacextend.TyNil), (let coqpp_body () = 
                                                          Vernacextend.vtdefault (fun () -> 
                                                          
# 15 "src/g_waterproof.mlg"
     
      Feedback.msg_notice (strbrk "Hello world!")
    
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Tacentries.tactic_extend "coq-waterproof.plugin" "tactid" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("tactid", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                          Tacentries.TyNil)), 
           (fun i ist -> 
# 22 "src/g_waterproof.mlg"
     
      test(i)
    
           )))]

