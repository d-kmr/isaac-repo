open Notations
open PrintTools

module Path = struct
  (* Note: paths must be full path *)
  
  type sPath = string (* paths in the string form (eg. "/usr/local/bin") *)
            
  type lPath = string list  (* paths in the list form (eg. ["usr";"local";"bin"]) *)

  let remove_last_dirsep (path: sPath) =
    match String.get path (String.length path - 1) <> '/' with
    | true -> path
    | false -> Filename.dirname (path ^ "/_")

  let add_last_dirsep (path: sPath) = (remove_last_dirsep path) ^ "/"
             
  let s2l (path:sPath): lPath =
    List.filter (fun x -> x <> "") (String.split_on_char '/' (add_last_dirsep path))

  let l2s (path:lPath): sPath = "/" ^ (String.concat "/" path)
  
  let flatten_path str = String.map (fun c -> if c = '/' || c = '.' then '_' else c) str 

  let make_path dir tag name = dir ^ "/" ^ (flatten_path tag) ^ "___" ^ name
      
  let check_exist_file path = Sys.file_exists path
         
  let check_exist_directory path = try Sys.is_directory path with _ -> false

  let confirm_exist_directory path =
    match check_exist_directory path with
    | true -> ()
    | false -> (Fmt.printf "@[Error: No such directory: %s@." path; exit 0)
         
  let confirm_exist_file path : unit =
    match check_exist_file path with
    | true  -> ()
    | false -> (Fmt.printf "@[Error: No such file: %s@." path; exit 0)

  let get_parent (path: sPath) =
    match s2l path with
    | [] -> failwith "get_parent: no parent directory of the root";
    | lpath -> l2s (L.rev (L.tl (L.rev lpath)))

  let delete_directory_bool path =
    match check_exist_directory path with
    | true -> ignore(Unix.system (Fmt.sprintf "rm -fr %s" path)); true
    | false -> false

  let delete_directory (path: sPath) = let _ = delete_directory_bool path in ()
       
  let create_directory (path: sPath) = Unix.mkdir path 0o777

  let get_relative (start: sPath) (target: sPath): lPath =
    let rec cut_off path1 path2 =
      match path1,path2 with
      | [],_ -> path2
      | p1::path1',p2::path2' when p1=p2 -> cut_off path1' path2'
      | _,_ -> failwith (Fmt.sprintf "get_relative: invalid input: %s and %s" (l2s path1) (l2s path2));
    in
    cut_off (s2l start) (s2l target)
                                     
  let rec_visit_and_exec (dirPath: sPath) (f: sPath -> unit) =
    let rec aux dirPath =
      let filesdirPath = L.map (fun x -> (dirPath ^ "/" ^ x)) (Array.to_list (Sys.readdir dirPath)) in
      let (subdirPath, filePath) = List.partition Sys.is_directory filesdirPath in
      List.iter f filePath;
      List.iter aux subdirPath
    in
    aux dirPath
    
end
;;

module Env = struct
  (* Global information *)

  let slacDir = ref "" (* slac directory *)
  let set_slacDir dir = slacDir := Path.remove_last_dirsep dir
  let get_slacDir () = !slacDir
  
  let projectDir = ref "" (* Project Directory *)
  let set_projectDir dir = projectDir := Path.remove_last_dirsep dir
  let get_projectDir () = !projectDir

  let slacdata = ref "SlacData" (* slacdata directory name (default:"SlacData") *)
  let set_slacdata name = slacdata := name
  let get_slacdata () = !slacdata
                  
  let get_SlacData_dir () = Fmt.sprintf "%s/%s" !projectDir !slacdata

  let get_ParsedCabs_dir () =  Fmt.sprintf "%s/%s/ParsedCabs" !projectDir !slacdata

  let get_Parsed_dir () =  Fmt.sprintf "%s/%s/Parsed" !projectDir !slacdata
                         
  let get_Captured_dir () = Fmt.sprintf "%s/%s/Captured" !projectDir !slacdata
                         
  let get_Translated_dir () = Fmt.sprintf "%s/%s/Translated" !projectDir !slacdata

  let get_Compacted_dir () = Fmt.sprintf "%s/%s/Translated/Compacted" !projectDir !slacdata

  let get_slacCapture_dir () = Fmt.sprintf "%s/slacCapture" !slacDir
    
  let get_compiler_dir () = Fmt.sprintf "%s/slacCapture/compiler" !slacDir

  let get_fbPlugIn () = Fmt.sprintf "%s/slacCapture/compiler/FacebookClangPlugin.dylib" !slacDir

  let get_fbClang () = Fmt.sprintf "%s/slacCapture/compiler/clang" !slacDir

  let get_myclang () = Fmt.sprintf "%s/slacCapture/clang" !slacDir

  let get_mygcc () = Fmt.sprintf "%s/slacCapture/gcc" !slacDir
                         
  (* The absolute path of the directory where functions are saved as marshalled file *)
  let get_func_dir () = Fmt.sprintf "%s/%s/Translated/func" !projectDir !slacdata

  let toplevelFunc = ref "" (* toplevel function for analysis *)
  let set_toplevelFunc fname = toplevelFunc := fname
  let get_toplevelFunc () = !toplevelFunc
                      
  let srcfile = ref ""
  let set_srcfile file = srcfile := file
  let get_srcfile () = !srcfile

  let currentfunc = ref ""   (** The current function *)
  let set_currentfunc f = currentfunc := f
  let get_currentfunc () = !currentfunc

  let funcallfile = ref ""
  let set_funcallfile file = funcallfile := file
  let get_funcallfile () = !funcallfile
                   
  let num = ref 0

  let addr = ref 1

  let newaddr () = addr := (!addr + 8); (string_of_int !addr)

  let new_prog_var _ =
    let t = Fmt.sprintf "%s#_%d" !currentfunc !num in
    num := !num + 1;
    t

  let moduleId = ref 0
  let set_moduleId n = moduleId := n
  let get_moduleId () = !moduleId
                      
  let get_fpa_dir () =  Fmt.sprintf "%s/%s/Fpa" !projectDir !slacdata;;
  let get_fpa_fundef_dir () = Fmt.sprintf "%s/%s/Fpa/Fundef" !projectDir !slacdata;;
  let get_fpa_global_data_dir () =  Fmt.sprintf "%s/%s/Fpa/GlobalData" !projectDir !slacdata;;
  let get_fpa_profile_dir () = Fmt.sprintf "%s/%s/Fpa/Profiles" !projectDir !slacdata;;

  let add_env_path p = Unix.putenv "PATH" (p ^ ":" ^ (Unix.getenv "PATH"))

  let show_env_path () = Fmt.printf "@[PATH = %s@." (Unix.getenv "PATH")

end
;;               
            
module IO = struct
  
  let write_file filename data =
    let fout = open_out filename in
    Marshal.to_channel fout data [];
    close_out fout

  let read_file filename =
    let fin = open_in filename in
    try
      let data = Marshal.from_channel fin in
      close_in fin;
      data
    with
    | End_of_file ->
       close_in_noerr fin;
       raise End_of_file
    | e ->
       close_in_noerr fin;
       raise e

  let write_file_string filename str =
    let fout = open_out filename in
    output_string fout str;
    close_out fout
       
  (* Reading all files in dirpath + left-folding *)
  (* Give a function f : <D:folded data> -> <A:unMarchaled data> -> <A*D: folded data> *)
  (* Type information is necessary *)
  let read_and_fold (f: 'a-> 'b -> 'a)  (v: 'a) dirpath =
    (* Note: an unMarshaled file has type 'b and a folded data has type 'a *)
    let counter = ref 0 in
    let files_arr = Sys.readdir dirpath in
    Array.sort String.compare files_arr;
    let files = Array.to_list files_arr in
    print_int (List.length files); print_string " files: "; flush_all ();
    let f1 dat file =
      let filepath = dirpath ^ "/" ^ file in
      if !counter < 10 then counter := !counter + 1 else (counter := 0;print_string ".";flush_all ());
      if Sys.is_directory filepath
      then dat
      else 
        begin
          dbg "DONES" "Reading:" p filepath;
          let b = read_file filepath in
          f dat b
        end
    in
    let res = List.fold_left f1 v files in
    print_newline ();
    res

  (* Reading all files in dirpath. *)
  (* It returns a list of unMarchaled files (type information is necessary) *)
  let read_allfiles dirpath = read_and_fold (fun bL b -> b :: bL) [] dirpath
                            
end
;;

module Debug = struct

  let write tag ?(header="") filename pp (data: 'a) =
    if (tag |<- !p_opt)
    then
      begin
        let cout = open_out filename in
        let fout = Fmt.formatter_of_out_channel cout in
        if header != "" then Fmt.fprintf fout "@[%s@." header;
        Fmt.fprintf fout "@[%a@." pp data;
        close_out cout
      end
    else
      ()

end
;;
