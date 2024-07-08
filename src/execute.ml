
open Output

module Host = struct

    (* We build on top of this host, wrapping it inside the type [out]. *)
    module Host = Shim.DummyHost

    type host_function = Host.host_function
    let host_function_eq_dec = Host.host_function_eq_dec

    type 'a host_event = 'a out Host.host_event
    let host_ret v = Host.host_ret (OK v)
    let host_bind v cont =
      Host.host_bind v (function
        | OK v -> cont v
        | Error msg -> Host.host_ret (Error msg))

    let host_apply st t h vs =
      Host.host_bind (Host.host_apply st t h vs) (fun r -> host_ret r)

    let show_host_function = Host.show_host_function

    let error msg = Host.host_ret (Error msg)

    let pmatch ok error v =
      Host.host_bind v (function
        | OK v -> host_ret (ok v)
        | Error msg -> host_ret (error msg))

    let from_out = function
      | OK v -> host_ret v
      | Error msg -> error msg

    exception ToOut of string

    let to_out v =
      (* FIXME: This is not the nicest code ever. *)
      try OK (pmatch (fun x -> x) (fun msg -> raise (ToOut msg)) v)
      with ToOut msg -> Error msg

  end

module Interpreter = Shim.Interpreter (Host)

(** An alias of [Host] to be able to retrieve it later. *)
module TopHost = Host

open Host
open Interpreter
(*
let config_tuple_patch cfg =
  let ((s, f), es) = cfg in
  (((Obj.magic s, s), f), es)

let config_tuple_patch_flat cfg =
  let ((s, f), es) = cfg in
  (Obj.magic s, s, f, es)
*)
(* read-eval-print loop; work in progress *)
let rec user_input prompt cb st =
  match LNoise.linenoise prompt with
  | None -> pure ()
  | Some v ->
    let* st' = cb v st in
    user_input prompt cb st'

let string_of_crash_reason = function
  | () -> "error"

(* XXX fix this in Coq? *)
let tuple_drop_hs res =
  match res with
  | (((_, s), f), r) -> ((s, f), r)

let take_step verbosity _i cfg =
  let res = run_step cfg in
  (*
  let ((s', _), _)  = (*Convert.from_triple*) res in
  let store_status = if s = s' then "unchanged" else "changed" in
  debug_info result verbosity (fun _ ->
    Printf.sprintf "%sand store %s\n%!" (pp_res_tuple_except_store (tuple_drop_hs res)) store_status) ;*)
  match (*Convert.from_triple*) res with
  | Extract.RSP_exhaustion ->
    debug_info result verbosity ~style:red (fun _ -> "exhaustion:") ;
    debug_info result verbosity (fun _ -> " " ^ string_of_crash_reason ()) ;
    pure cfg
  | Extract.RSP_terminal _ ->
    debug_info result verbosity ~style:red (fun _ -> "terminal") ;
    pure cfg
  | Extract.RSP_cfg _ ->
    pure cfg
(*
    type positive =
    | XI of positive
    | XO of positive
    | XH
    
    type n =
    | N0
    | Npos of positive
    *)

let rec int_of_pos p =
  match p with
  | Extract.XI p' -> 2 * (int_of_pos p') + 1
  | Extract.XO p' -> 2 * (int_of_pos p')
  | Extract.XH -> 1

let int_of_N n =
  match n with
  | Extract.N0 -> 0
  | Extract.Npos p -> int_of_pos p

let sies_to_cfg (name: string) sies = 
  match lookup_exported_function name sies with
  | None -> Error ("unknown function `" ^ name ^ "`")
  | Some (((_, s), f), addr) -> 
    match run_init_invoke s f addr with 
    | Some cfg -> OK cfg
    | None -> Error ("Invocation failed to typecheck")

    (*
let repl verbosity sies (name : string) =
  LNoise.set_hints_callback (fun line ->
      (* FIXME: Documentation is needed here. I don’t know what these lines do. *)
      if line <> "git remote add " then None
      else Some (" <this is the remote name> <this is the remote URL>",
                 LNoise.Yellow,
                 true)
    );
  LNoise.history_load ~filename:"history.txt" |> ignore;
  LNoise.history_set ~max_length:100 |> ignore;
  LNoise.set_completion_callback begin fun line_so_far ln_completions ->
    (if line_so_far = "" then
      ["store"]
    else if line_so_far <> "" && line_so_far.[0] = 's' then
      ["store"]
    else [])
      |> List.iter (LNoise.add_completion ln_completions);
  end;
  ["interactive Wasm interpreter";
   "get tab completion with <TAB>";
   "type quit to exit gracefully"]
  |> List.iter print_endline;
  match sies_to_cfg name sies with
  | Error err -> error err
  | OK cfg0 ->
    debug_info result verbosity (fun _ ->
      Printf.sprintf "\n%s"
        (pp_res_tuple_except_store cfg0)) ;
    (fun from_user cfg ->
      if from_user = "quit" then exit 0;
      LNoise.history_add from_user |> ignore;
      LNoise.history_save ~filename:"history.txt" |> ignore;
      if from_user = "" || from_user = "step" then take_step verbosity cfg
      else if from_user = "help" then
        (Printf.sprintf "commands:\nstep: take a step\nstore: display the store\nquit: quit\nhelp: this help message" |> print_endline;
         pure cfg)
      else (Printf.sprintf "unknown command" |> print_endline; pure cfg))
    |> (fun cb -> user_input "> " cb cfg0)
*)
let interpret verbosity error_code_on_crash sies (name: string) =
  let print_step_header gen =
    debug_info verbosity intermediate ~style:bold
      (fun () -> Printf.sprintf "step %d:\n" gen) in
  (*let print_exhaustion gen = 
    debug_info verbosity intermediate ~style:bold
      (fun () -> Printf.sprintf "step %d: \n Execution halted due to fuel exhaustion\n" gen) in*)
  let* cfg0 =
    TopHost.from_out (
      ovpending verbosity stage "interpreting" (fun _ ->
        sies_to_cfg name sies
        )) in
  let rec eval_cfg gen cfg max_size total_size =
   (* if (gen >= max_steps) then 
      (print_exhaustion gen;
      debug_info verbosity result ~style:bold (fun _ -> "fuel exhaustion\n");
      pure None)
    else *)
      (let cfg_res = run_step cfg in
      let ppi_size = (int_of_N (sizeof_ppi cfg_res)) in
      print_step_header gen ;
      debug_info verbosity intermediate
        (fun _ -> pp_res_tuple_except_store_typed cfg_res);
        
      debug_info verbosity stage
        (fun _ -> "Size of proof term : " ^ string_of_int (int_of_N (sizeof_ppi cfg_res)));
        (*
      debug_info_span verbosity intermediate intermediate
        (fun () ->
          let (((_, s), _), _) = cfg in
          let (((_, s'), _), _) = cfg_res in
          let store_status = if s = s' then "unchanged" else "changed" in
          Printf.sprintf "and store %s\n" store_status); 
      debug_info verbosity store
        (fun () ->
          let (((_, s'), _), _) = cfg_res in
          Printf.sprintf "and store\n%s" (pp_store 1 s'));*)
      match cfg_res with
      | Extract.RSP_exhaustion ->
        wait_message verbosity;
        debug_info verbosity result ~style:red (fun _ -> "crash\n");
        pure None
      | Extract.RSP_cfg (_, s, f, es, ts, p) ->
        wait_message verbosity;
        debug_info verbosity stage ~style:green (fun _ -> "cfg\n");
        eval_cfg (gen + 1) cfg_res (max ppi_size max_size) (total_size + ppi_size)
      | Extract.RSP_terminal (es, p) ->
        begin match is_const_list es with
        | Some vs -> 
          debug_info verbosity result ~style:green (fun _ -> "success after " ^ string_of_int gen ^ " steps\n maximum/average proof size = " ^ string_of_int max_size ^ "/" ^ string_of_float ((float_of_int total_size) /. (float_of_int gen)) ^ "\n");
          pure (Some vs)
        | None -> 
          debug_info verbosity result ~style:red (fun _ -> "termination with a non-value\n"); 
          pure None
        end) in
  
  let start_time = Sys.time() in
  debug_info verbosity result ~style:yellow (fun _ -> "PPI Interpreter\n");
  print_step_header 0 ;
  debug_info verbosity intermediate (fun _ ->
    Printf.sprintf "\n%s\n" (pp_res_tuple_except_store_typed cfg0));
  let* res = eval_cfg 1 cfg0 0 0 in
  debug_info_span verbosity result stage (fun _ ->
    match res with
    | Some vs -> pp_values vs
    | None -> "");
  Printf.printf "Execution time: %fs\n" (Sys.time() -. start_time);
  if error_code_on_crash && (match res with None -> true | Some _ -> false) then exit 1
  else pure ()

(* TODO: update the interactive to use the context-optimised version as well *)
let instantiate_interpret verbosity interactive error_code_on_crash m name =
  let* store_inst_exps =
    TopHost.from_out (
      ovpending verbosity stage "instantiation" (fun _ ->
        match interp_instantiate_wrapper m with
        | None -> Error "instantiation error"
        | Some (store_inst_exps, _) -> OK store_inst_exps)) in
  if interactive then (*repl*) interpret verbosity error_code_on_crash store_inst_exps name
  else interpret verbosity error_code_on_crash store_inst_exps name
