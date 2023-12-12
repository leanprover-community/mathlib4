// Lean compiler output
// Module: Cache.Requests
// Imports: Init Lean.Data.Json.Parser Cache.Hashing
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Cache_Requests_checkForToolchainMismatch___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
extern lean_object* l_Cache_IO_CURLCFG;
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__11;
static lean_object* l_Cache_Requests_downloadFiles___lambda__9___closed__2;
uint8_t l_String_endsWith(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_mkFileURL___closed__2;
lean_object* l_EIO_toBaseIO___rarg(lean_object*, lean_object*);
lean_object* l_UInt64_asLTar(uint64_t);
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__8;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__5;
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__2;
static lean_object* l_Cache_Requests_putFiles___closed__23;
LEAN_EXPORT lean_object* l_Cache_Requests_getFiles___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_HashMap_toArray___at_Cache_Requests_mkGetConfigContent___spec__1___closed__1;
static lean_object* l_Cache_Requests_downloadFiles___lambda__7___closed__2;
lean_object* l_Cache_IO_runCurlStreaming___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_isGitStatusClean___closed__5;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__19;
lean_object* lean_array_data(lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__7___closed__3;
lean_object* l_Cache_IO_HashMap_filterExists(lean_object*, uint8_t, lean_object*);
static lean_object* l_Cache_Requests_commit___closed__15;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_formatError___rarg___closed__2;
static lean_object* l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___closed__1;
static lean_object* l_Cache_Requests_downloadFile___closed__3;
lean_object* lean_io_remove_file(lean_object*, lean_object*);
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_downloadFile___closed__5;
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__11(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Option_Basic_0__decEqOption____x40_Init_Data_Option_Basic___hyg_965____at_instDecidableEqOption___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__12;
LEAN_EXPORT lean_object* l_Cache_Requests_putFiles___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l_Cache_Requests_putFiles___closed__14;
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__20;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__11;
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles(lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Cache_Requests_putFiles___closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__4;
static lean_object* l_Cache_Requests_mkFileURL___closed__4;
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Cache_Requests_downloadFiles___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__3;
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__21;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_putFiles___closed__11;
lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__1;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__22;
static lean_object* l_Cache_Requests_getGitCommitHash___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Cache_Requests_mkFileURL(lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__9___closed__1;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__14;
lean_object* lean_io_rename(lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_putFiles___closed__25;
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_desc___boxed(lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__17;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__21;
lean_object* l_String_trim(lean_object*);
lean_object* l_Cache_IO_mkDir(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__7;
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__17;
static lean_object* l_Cache_Requests_commit___closed__10;
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_prefix___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Cache_Requests_downloadFiles___spec__2(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__3;
static lean_object* l_Cache_Requests_commit___closed__4;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__9;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_commit___closed__5;
lean_object* l_List_head_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__1(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__4___closed__5;
static lean_object* l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__2;
static lean_object* l_Cache_Requests_putFiles___closed__5;
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__15;
static lean_object* l_Cache_Requests_commit___closed__2;
static lean_object* l_Cache_Requests_getFilesInfo___closed__3;
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__10;
LEAN_EXPORT lean_object* l_Cache_Requests_getFiles(lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_commit(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_putFiles___closed__7;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_URL;
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__5___closed__1;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__12;
static lean_object* l_Cache_Requests_commit___closed__13;
static lean_object* l_Cache_Requests_QueryType_desc___closed__2;
static lean_object* l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Cache_Requests_getFiles___lambda__1(lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_commit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__4___closed__4;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static lean_object* l_Cache_Requests_getFilesInfo___closed__5;
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
lean_object* l_Cache_IO_runCurl(lean_object*, uint8_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_String_isEmpty(lean_object*);
static lean_object* l_Cache_Requests_QueryType_prefix___closed__1;
static lean_object* l_Cache_Requests_downloadFiles___lambda__4___closed__3;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__24;
lean_object* lean_io_mono_ms_now(lean_object*);
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__6;
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__20;
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_dropRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_checkForToolchainMismatch___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_putFiles___closed__20;
static lean_object* l_Cache_Requests_putFiles___closed__21;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__23;
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__16;
static lean_object* l_Cache_Requests_downloadFile___closed__1;
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFile(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_getGitCommitHash___closed__3;
static lean_object* l_Cache_Requests_downloadFiles___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Cache_Requests_getGitCommitHash(lean_object*);
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__4;
LEAN_EXPORT lean_object* l_Cache_Requests_getFiles___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_commit___closed__16;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Cache_Requests_commit___spec__3(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_putFiles___closed__9;
lean_object* l_Cache_IO_unpackCache(lean_object*, uint8_t, lean_object*);
static lean_object* l_Cache_Requests_getFilesInfo___closed__6;
LEAN_EXPORT lean_object* l_Cache_Requests_mkFileURL___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__1;
lean_object* lean_uint64_to_nat(uint64_t);
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__3;
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Cache_Requests_mkGetConfigContent___spec__2(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_mkFileURL___closed__5;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__15;
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__18;
static lean_object* l_Cache_Requests_commit___closed__3;
static lean_object* l_Cache_Requests_commit___closed__11;
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Cache_Requests_mkGetConfigContent___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__5;
static lean_object* l_Cache_Requests_formatError___rarg___closed__1;
lean_object* l_System_FilePath_components(lean_object*);
lean_object* l_Cache_IO_runCmd(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_downloadFiles___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_putFiles___closed__4;
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Cache_Requests_commit___spec__2(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_mkFileURL___closed__3;
static lean_object* l_Cache_Requests_downloadFiles___lambda__4___closed__1;
static lean_object* l_Cache_Requests_isGitStatusClean___closed__2;
LEAN_EXPORT lean_object* l_Cache_Requests_getFilesInfo(uint8_t, lean_object*);
static lean_object* l_Cache_Requests_isGitStatusClean___closed__3;
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_noConfusion___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__2;
static lean_object* l_Cache_Requests_commit___closed__7;
lean_object* l_Cache_IO_getCurl(lean_object*);
lean_object* l_IO_ofExcept___at_IO_FS_Stream_readJson___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_prefix(uint8_t);
LEAN_EXPORT lean_object* l_Cache_Requests_putFiles___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_checkForToolchainMismatch(lean_object*);
static lean_object* l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Cache_Requests_formatError___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_mkPutConfigContent(lean_object*, lean_object*, lean_object*);
lean_object* l_Cache_IO_HashMap_hashes(lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__10;
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__9;
lean_object* lean_task_get_own(lean_object*);
extern lean_object* l_Cache_IO_mathlibDepPath;
static lean_object* l_Cache_Requests_putFiles___closed__6;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__1;
static lean_object* l_Cache_Requests_getFilesInfo___closed__4;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__4(lean_object*, lean_object*);
extern lean_object* l_Cache_IO_CACHEDIR;
static lean_object* l_Cache_Requests_putFiles___closed__16;
static lean_object* l_Cache_Requests_putFiles___closed__13;
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_putFiles___closed__15;
static lean_object* l_Cache_Requests_mkFileURL___closed__1;
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_toCtorIdx(uint8_t);
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__22;
static lean_object* l_Cache_Requests_downloadFiles___lambda__4___closed__7;
static lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__5;
static lean_object* l_Cache_Requests_getGitCommitHash___closed__4;
static lean_object* l_Cache_Requests_commit___closed__8;
LEAN_EXPORT lean_object* l_Cache_Requests_formatError(lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_putFiles(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_commit___closed__12;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__4;
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_commit___closed__14;
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_isGitStatusClean(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_putFiles___closed__22;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Cache_Requests_putFiles___closed__12;
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_desc(uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_downloadFiles___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__18;
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__19;
static lean_object* l_Cache_Requests_putFiles___closed__24;
static lean_object* l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__2;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__13;
LEAN_EXPORT lean_object* l_Cache_Requests_getFilesInfo___boxed(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_getFilesInfo___closed__1;
static lean_object* l_Cache_Requests_putFiles___closed__18;
lean_object* lean_io_exit(uint8_t, lean_object*);
static lean_object* l_Cache_Requests_getGitCommitHash___closed__2;
static lean_object* l_Cache_Requests_putFiles___closed__1;
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_mkGetConfigContent(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__13;
static lean_object* l_Cache_Requests_putFiles___closed__3;
static lean_object* l_Cache_Requests_getFilesInfo___closed__2;
static lean_object* l_Cache_Requests_isGitStatusClean___closed__1;
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
static lean_object* l_Cache_Requests_commit___closed__1;
static lean_object* l_Cache_Requests_putFiles___closed__10;
static lean_object* l_Cache_Requests_commit___closed__17;
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__6;
static lean_object* l_Cache_Requests_downloadFiles___lambda__4___closed__2;
static lean_object* l_Cache_Requests_downloadFiles___lambda__4___closed__6;
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_QueryType_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Cache_Requests_downloadFile___closed__4;
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_putFiles___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_commit___closed__9;
static lean_object* l_Cache_Requests_putFiles___closed__17;
static lean_object* l_Cache_Requests_downloadFiles___lambda__7___closed__1;
static lean_object* l_Cache_Requests_putFiles___closed__19;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_commit___closed__6;
static lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__16;
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Cache_Requests_commit___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_checkForToolchainMismatch___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_QueryType_prefix___closed__2;
static lean_object* l_Cache_Requests_downloadFile___closed__2;
static lean_object* l_Cache_Requests_QueryType_desc___closed__1;
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_trimRight(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_checkForToolchainMismatch___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Cache_IO_isMathlibRoot(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___at_Cache_Requests_commit___spec__1(lean_object*);
static lean_object* l_Cache_Requests_putFiles___closed__26;
static lean_object* l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__2;
lean_object* l_IO_eprint___at_IO_eprintln___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__8;
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__14;
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Cache_Requests_downloadFiles___lambda__11___closed__7;
LEAN_EXPORT lean_object* l_Lean_HashMap_toArray___at_Cache_Requests_mkGetConfigContent___spec__1(lean_object*);
static lean_object* l_Cache_Requests_putFiles___closed__8;
static lean_object* l_Cache_Requests_isGitStatusClean___closed__6;
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__1;
static lean_object* l_Cache_Requests_checkForToolchainMismatch___closed__1;
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_toCtorIdx___boxed(lean_object*);
static lean_object* l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__3;
static lean_object* l_Cache_Requests_downloadFiles___lambda__9___closed__3;
static lean_object* l_Cache_Requests_QueryType_desc___closed__3;
static lean_object* l_Cache_Requests_isGitStatusClean___closed__4;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_String_splitOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__11___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Cache_Requests_URL___closed__1;
static lean_object* _init_l_Cache_Requests_URL___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("https://lakecache.blob.core.windows.net/mathlib4", 48);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_URL() {
_start:
{
lean_object* x_1; 
x_1 = l_Cache_Requests_URL___closed__1;
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_mkFileURL___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_mkFileURL___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_mkFileURL___closed__1;
x_2 = l_Cache_Requests_URL;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_mkFileURL___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("/f/", 3);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_mkFileURL___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_mkFileURL___closed__2;
x_2 = l_Cache_Requests_mkFileURL___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_mkFileURL___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\?", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_mkFileURL(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Cache_Requests_mkFileURL___closed__4;
x_5 = lean_string_append(x_4, x_1);
x_6 = l_Cache_Requests_mkFileURL___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = l_Cache_Requests_mkFileURL___closed__4;
x_11 = lean_string_append(x_10, x_1);
x_12 = l_Cache_Requests_mkFileURL___closed__5;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_13, x_9);
x_15 = l_Cache_Requests_mkFileURL___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_mkFileURL___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Cache_Requests_mkFileURL(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Cache_Requests_mkGetConfigContent___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_AssocList_foldlM___at_Cache_Requests_mkGetConfigContent___spec__2(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lean_HashMap_toArray___at_Cache_Requests_mkGetConfigContent___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_toArray___at_Cache_Requests_mkGetConfigContent___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Lean_HashMap_toArray___at_Cache_Requests_mkGetConfigContent___spec__1___closed__1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_HashMap_toArray___at_Cache_Requests_mkGetConfigContent___spec__1___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Lean_HashMap_toArray___at_Cache_Requests_mkGetConfigContent___spec__1___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__3(x_2, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
}
}
static lean_object* _init_l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("MathlibExtras", 13);
return x_1;
}
}
static lean_object* _init_l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_decEq___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_System_FilePath_components(x_3);
x_5 = l_List_head_x3f___rarg(x_4);
lean_dec(x_4);
x_6 = l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__3;
x_7 = l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__2;
x_8 = l___private_Init_Data_Option_Basic_0__decEqOption____x40_Init_Data_Option_Basic___hyg_965____at_instDecidableEqOption___spec__1___rarg(x_6, x_5, x_7);
return x_8;
}
}
static lean_object* _init_l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___closed__1;
lean_inc(x_2);
x_6 = l_Array_qpartition___rarg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("url = ", 6);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n-o ", 4);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".part", 5);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Cache_IO_CACHEDIR;
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = l_UInt64_asLTar(x_9);
x_11 = lean_box(0);
x_12 = l_Cache_Requests_mkFileURL(x_10, x_11, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__1;
x_16 = lean_string_append(x_15, x_13);
lean_dec(x_13);
x_17 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__3;
x_20 = lean_string_append(x_10, x_19);
x_21 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__4;
x_22 = l_System_FilePath_join(x_21, x_20);
x_23 = l_String_quote(x_22);
lean_dec(x_22);
x_24 = lean_string_append(x_18, x_23);
lean_dec(x_23);
x_25 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__5;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_4, x_26);
lean_dec(x_26);
x_28 = 1;
x_29 = lean_usize_add(x_2, x_28);
x_2 = x_29;
x_4 = x_27;
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_mkGetConfigContent(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = l_Lean_HashMap_toArray___at_Cache_Requests_mkGetConfigContent___spec__1(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4(x_3, x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_get_size(x_8);
x_10 = lean_nat_dec_lt(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Cache_Requests_mkFileURL___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_9, x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_Cache_Requests_mkFileURL___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_18 = l_Cache_Requests_mkFileURL___closed__1;
x_19 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5(x_8, x_16, x_17, x_18, x_2);
lean_dec(x_8);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Cache_Requests_mkGetConfigContent___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_foldlM___at_Cache_Requests_mkGetConfigContent___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Cache_Requests_downloadFile___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Cache_Requests_downloadFile___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Cache_Requests_downloadFile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--fail", 6);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFile___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--silent", 8);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFile___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-o", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFile(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_3 = l_UInt64_asLTar(x_1);
x_4 = lean_box(0);
x_5 = l_Cache_Requests_mkFileURL(x_3, x_4, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__4;
lean_inc(x_3);
x_9 = l_System_FilePath_join(x_8, x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__3;
x_11 = lean_string_append(x_3, x_10);
x_12 = l_System_FilePath_join(x_8, x_11);
x_13 = l_Cache_IO_getCurl(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Cache_Requests_downloadFile___closed__2;
x_17 = lean_array_push(x_16, x_6);
x_18 = l_Cache_Requests_downloadFile___closed__3;
x_19 = lean_array_push(x_17, x_18);
x_20 = l_Cache_Requests_downloadFile___closed__4;
x_21 = lean_array_push(x_19, x_20);
x_22 = l_Cache_Requests_downloadFile___closed__5;
x_23 = lean_array_push(x_21, x_22);
lean_inc(x_12);
x_24 = lean_array_push(x_23, x_12);
x_25 = l_Cache_Requests_downloadFile___closed__1;
x_26 = l_Lean_HashMap_toArray___at_Cache_Requests_mkGetConfigContent___spec__1___closed__1;
x_27 = 0;
x_28 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_14);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_4);
lean_ctor_set(x_28, 4, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*5, x_27);
x_29 = l_IO_Process_output(x_28, x_15);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint32_t x_32; uint32_t x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get_uint32(x_30, sizeof(void*)*2);
lean_dec(x_30);
x_33 = 0;
x_34 = lean_uint32_dec_eq(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_9);
x_35 = lean_io_remove_file(x_12, x_31);
lean_dec(x_12);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(x_27);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(x_27);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
x_46 = lean_io_rename(x_12, x_9, x_31);
lean_dec(x_9);
lean_dec(x_12);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = 1;
x_50 = lean_box(x_49);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = 1;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_46);
if (x_55 == 0)
{
return x_46;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_46, 0);
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_46);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_12);
lean_dec(x_9);
x_59 = !lean_is_exclusive(x_29);
if (x_59 == 0)
{
return x_29;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_29, 0);
x_61 = lean_ctor_get(x_29, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_29);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Cache_Requests_downloadFile(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Cache_Requests_downloadFiles___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Cache_Requests_downloadFile___boxed), 2, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Task_Priority_default;
x_10 = lean_io_as_task(x_8, x_9, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_1);
x_1 = x_13;
x_2 = x_6;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Cache_Requests_downloadFiles___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_task_get_own(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
lean_dec(x_1);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_4;
goto _start;
}
else
{
x_2 = x_4;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_downloadFiles___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = l_Lean_AssocList_foldlM___at_Cache_Requests_downloadFiles___spec__1(x_4, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getNat_x3f(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" download(s) failed", 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Nat_repr(x_1);
x_8 = l_Cache_Requests_mkFileURL___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Cache_Requests_downloadFiles___lambda__1___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_IO_println___at_Lean_instEval___spec__1(x_11, x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = 1;
x_15 = lean_io_exit(x_14, x_13);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_eprint___at_IO_eprintln___spec__1(x_7, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_12, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\rDownloaded: ", 13);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" file(s) [attempted ", 20);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("/", 1);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" = ", 3);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("%]", 2);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__4___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" failed", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_12 = lean_io_mono_ms_now(x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_nat_sub(x_13, x_6);
x_16 = lean_unsigned_to_nat(100u);
x_17 = lean_nat_dec_le(x_16, x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = lean_apply_6(x_1, x_11, x_5, x_6, x_7, x_18, x_14);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_inc(x_7);
x_20 = l_Nat_repr(x_7);
x_21 = l_Cache_Requests_downloadFiles___lambda__4___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Cache_Requests_downloadFiles___lambda__4___closed__2;
x_24 = lean_string_append(x_22, x_23);
lean_inc(x_11);
x_25 = l_Nat_repr(x_11);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = l_Cache_Requests_downloadFiles___lambda__4___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_28, x_2);
lean_dec(x_2);
x_30 = l_Cache_Requests_downloadFiles___lambda__4___closed__4;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_nat_mul(x_16, x_11);
x_33 = lean_nat_div(x_32, x_3);
lean_dec(x_3);
lean_dec(x_32);
x_34 = l_Nat_repr(x_33);
x_35 = lean_string_append(x_31, x_34);
lean_dec(x_34);
x_36 = l_Cache_Requests_downloadFiles___lambda__4___closed__5;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_5, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc(x_5);
x_40 = l_Nat_repr(x_5);
x_41 = l_Cache_Requests_downloadFiles___lambda__4___closed__6;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = l_Cache_Requests_downloadFiles___lambda__4___closed__7;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_string_append(x_37, x_44);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = l_Cache_Requests_downloadFiles___lambda__3(x_1, x_11, x_5, x_13, x_7, x_6, x_45, x_46, x_14);
lean_dec(x_6);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(0);
x_49 = l_Cache_Requests_downloadFiles___lambda__3(x_1, x_11, x_5, x_13, x_7, x_6, x_37, x_48, x_14);
lean_dec(x_6);
return x_49;
}
}
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("filename_effective", 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Cache_Requests_downloadFiles___lambda__5___closed__1;
x_10 = l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__5(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_11, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_System_FilePath_pathExists(x_13, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_18, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_io_remove_file(x_13, x_20);
lean_dec(x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_22, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_5, x_8);
x_10 = lean_box(0);
x_11 = lean_apply_6(x_1, x_2, x_3, x_4, x_9, x_10, x_7);
return x_11;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Cache_Requests_downloadFiles___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("http_code", 9);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("errormsg", 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_String_trim(x_4);
lean_dec(x_4);
x_13 = l_Cache_Requests_downloadFiles___lambda__7___closed__1;
x_14 = l_String_isEmpty(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Json_parse(x_12);
x_16 = l_IO_ofExcept___at_IO_FS_Stream_readJson___spec__1(x_15, x_5);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_2);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Cache_Requests_downloadFiles___lambda__4), 9, 3);
lean_closure_set(x_19, 0, x_13);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
x_20 = l_Cache_Requests_downloadFiles___lambda__7___closed__2;
x_21 = l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__4(x_17, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_10, x_22);
lean_dec(x_10);
x_24 = l_Cache_Requests_downloadFiles___lambda__7___closed__3;
x_25 = l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__5(x_17, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_25);
x_26 = lean_box(0);
x_27 = l_Cache_Requests_downloadFiles___lambda__5(x_17, x_19, x_11, x_23, x_8, x_9, x_26, x_18);
lean_dec(x_17);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_IO_println___at_Lean_instEval___spec__1(x_28, x_18);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Cache_Requests_downloadFiles___lambda__5(x_17, x_19, x_11, x_23, x_8, x_9, x_30, x_31);
lean_dec(x_30);
lean_dec(x_17);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_21, 0);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_unsigned_to_nat(200u);
x_39 = lean_nat_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_unsigned_to_nat(404u);
x_41 = lean_nat_dec_eq(x_37, x_40);
lean_dec(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_10, x_42);
lean_dec(x_10);
x_44 = l_Cache_Requests_downloadFiles___lambda__7___closed__3;
x_45 = l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__5(x_17, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_45);
x_46 = lean_box(0);
x_47 = l_Cache_Requests_downloadFiles___lambda__5(x_17, x_19, x_11, x_43, x_8, x_9, x_46, x_18);
lean_dec(x_17);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l_IO_println___at_Lean_instEval___spec__1(x_48, x_18);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Cache_Requests_downloadFiles___lambda__5(x_17, x_19, x_11, x_43, x_8, x_9, x_50, x_51);
lean_dec(x_50);
lean_dec(x_17);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_43);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_19);
lean_dec(x_17);
x_57 = lean_box(0);
x_58 = l_Cache_Requests_downloadFiles___lambda__4(x_13, x_1, x_2, x_11, x_10, x_8, x_9, x_57, x_18);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_59 = l_Cache_Requests_downloadFiles___lambda__5___closed__1;
x_60 = l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__5(x_17, x_59);
lean_dec(x_17);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_60);
x_61 = lean_box(0);
x_62 = l_Cache_Requests_downloadFiles___lambda__6(x_19, x_11, x_10, x_8, x_9, x_61, x_18);
lean_dec(x_9);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l_System_FilePath_pathExists(x_63, x_18);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_63);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_box(0);
x_69 = l_Cache_Requests_downloadFiles___lambda__6(x_19, x_11, x_10, x_8, x_9, x_68, x_67);
lean_dec(x_9);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
x_71 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__3;
lean_inc(x_63);
x_72 = l_String_endsWith(x_63, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_63);
x_73 = lean_box(0);
x_74 = l_Cache_Requests_downloadFiles___lambda__6(x_19, x_11, x_10, x_8, x_9, x_73, x_70);
lean_dec(x_9);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_unsigned_to_nat(5u);
lean_inc(x_63);
x_76 = l_String_dropRight(x_63, x_75);
x_77 = lean_io_rename(x_63, x_76, x_70);
lean_dec(x_76);
lean_dec(x_63);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Cache_Requests_downloadFiles___lambda__6(x_19, x_11, x_10, x_8, x_9, x_78, x_79);
lean_dec(x_78);
lean_dec(x_9);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_81 = !lean_is_exclusive(x_77);
if (x_81 == 0)
{
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_77, 0);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_77);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_16);
if (x_85 == 0)
{
return x_16;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_16, 0);
x_87 = lean_ctor_get(x_16, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_16);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_box(0);
x_90 = lean_apply_6(x_13, x_11, x_10, x_8, x_9, x_89, x_5);
return x_90;
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Warning: some files were not found in the cache.", 48);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__9___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("This usually means that your local checkout of mathlib4 has diverged from upstream.", 83);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__9___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("If you push your commits to a branch of the mathlib4 repository, CI will build the oleans and they will be available later.", 123);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Cache_IO_CURLCFG;
x_8 = lean_io_remove_file(x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_nat_add(x_3, x_2);
x_11 = lean_nat_dec_lt(x_10, x_4);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_apply_2(x_1, x_2, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Cache_Requests_downloadFiles___lambda__9___closed__1;
x_14 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_13, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Cache_Requests_downloadFiles___lambda__9___closed__2;
x_17 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_16, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Cache_Requests_downloadFiles___lambda__9___closed__3;
x_20 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_19, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_2(x_1, x_2, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_1, x_6, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("No files to download", 20);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Attempting to download ", 23);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" file(s)", 8);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Cache_Requests_downloadFiles___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--request", 9);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_downloadFiles___lambda__11___closed__5;
x_2 = l_Cache_Requests_downloadFiles___lambda__11___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("GET", 3);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_downloadFiles___lambda__11___closed__7;
x_2 = l_Cache_Requests_downloadFiles___lambda__11___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--parallel", 10);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_downloadFiles___lambda__11___closed__9;
x_2 = l_Cache_Requests_downloadFiles___lambda__11___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_downloadFiles___lambda__11___closed__11;
x_2 = l_Cache_Requests_downloadFile___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_downloadFiles___lambda__11___closed__12;
x_2 = l_Cache_Requests_downloadFile___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--write-out", 11);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_downloadFiles___lambda__11___closed__13;
x_2 = l_Cache_Requests_downloadFiles___lambda__11___closed__14;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("%{json}\n", 8);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_downloadFiles___lambda__11___closed__15;
x_2 = l_Cache_Requests_downloadFiles___lambda__11___closed__16;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--config", 8);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_downloadFiles___lambda__11___closed__17;
x_2 = l_Cache_Requests_downloadFiles___lambda__11___closed__18;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_downloadFiles___lambda__11___closed__19;
x_2 = l_Cache_IO_CURLCFG;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Cache_Requests_downloadFiles___lambda__11___closed__21;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("%] (", 4);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_downloadFiles___lambda__11___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("% success)", 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__11(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = l_Cache_Requests_downloadFiles___lambda__11___closed__1;
x_9 = l_IO_println___at_Lean_instEval___spec__1(x_8, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__4;
x_11 = l_Cache_IO_mkDir(x_10, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_4);
x_13 = l_Nat_repr(x_4);
x_14 = l_Cache_Requests_downloadFiles___lambda__11___closed__2;
x_15 = lean_string_append(x_14, x_13);
x_16 = l_Cache_Requests_downloadFiles___lambda__11___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_IO_println___at_Lean_instEval___spec__1(x_17, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Cache_Requests_downloadFiles___lambda__11___closed__4;
if (x_1 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_array_get_size(x_5);
x_23 = lean_nat_dec_lt(x_6, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_5);
x_24 = l_List_foldl___at_Cache_Requests_downloadFiles___spec__2(x_6, x_21);
x_25 = lean_apply_2(x_20, x_24, x_19);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_22, x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_5);
x_27 = l_List_foldl___at_Cache_Requests_downloadFiles___spec__2(x_6, x_21);
x_28 = lean_apply_2(x_20, x_27, x_19);
return x_28;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_31 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_downloadFiles___spec__3(x_5, x_29, x_30, x_21, x_19);
lean_dec(x_5);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_List_foldl___at_Cache_Requests_downloadFiles___spec__2(x_6, x_32);
x_35 = lean_apply_2(x_20, x_34, x_33);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_5);
x_36 = l_Cache_Requests_mkGetConfigContent(x_2, x_19);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Cache_IO_CURLCFG;
x_40 = l_IO_FS_writeFile(x_39, x_37, x_38);
lean_dec(x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_io_mono_ms_now(x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Cache_Requests_downloadFiles___lambda__11___closed__22;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_4);
lean_inc(x_13);
x_47 = lean_alloc_closure((void*)(l_Cache_Requests_downloadFiles___lambda__7), 5, 2);
lean_closure_set(x_47, 0, x_13);
lean_closure_set(x_47, 1, x_4);
x_48 = l_Cache_Requests_downloadFiles___lambda__11___closed__20;
x_49 = l_Cache_IO_runCurlStreaming___rarg(x_48, x_46, x_47, x_44);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
lean_inc(x_56);
lean_inc(x_54);
lean_inc(x_55);
x_57 = lean_alloc_closure((void*)(l_Cache_Requests_downloadFiles___lambda__9___boxed), 6, 4);
lean_closure_set(x_57, 0, x_20);
lean_closure_set(x_57, 1, x_55);
lean_closure_set(x_57, 2, x_54);
lean_closure_set(x_57, 3, x_56);
x_58 = lean_nat_dec_lt(x_6, x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_57);
lean_dec(x_13);
lean_dec(x_4);
x_59 = lean_box(0);
x_60 = l_Cache_Requests_downloadFiles___lambda__9(x_20, x_55, x_54, x_56, x_59, x_53);
lean_dec(x_56);
lean_dec(x_54);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_inc(x_54);
x_61 = l_Nat_repr(x_54);
x_62 = l_Cache_Requests_downloadFiles___lambda__4___closed__1;
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
x_64 = l_Cache_Requests_downloadFiles___lambda__4___closed__2;
x_65 = lean_string_append(x_63, x_64);
lean_inc(x_56);
x_66 = l_Nat_repr(x_56);
x_67 = lean_string_append(x_65, x_66);
lean_dec(x_66);
x_68 = l_Cache_Requests_downloadFiles___lambda__4___closed__3;
x_69 = lean_string_append(x_67, x_68);
x_70 = lean_string_append(x_69, x_13);
lean_dec(x_13);
x_71 = l_Cache_Requests_downloadFiles___lambda__4___closed__4;
x_72 = lean_string_append(x_70, x_71);
x_73 = lean_unsigned_to_nat(100u);
x_74 = lean_nat_mul(x_73, x_56);
x_75 = lean_nat_div(x_74, x_4);
lean_dec(x_4);
lean_dec(x_74);
x_76 = l_Nat_repr(x_75);
x_77 = lean_string_append(x_72, x_76);
lean_dec(x_76);
x_78 = l_Cache_Requests_downloadFiles___lambda__11___closed__23;
x_79 = lean_string_append(x_77, x_78);
x_80 = lean_nat_mul(x_73, x_54);
lean_dec(x_54);
x_81 = lean_nat_div(x_80, x_56);
lean_dec(x_56);
lean_dec(x_80);
x_82 = l_Nat_repr(x_81);
x_83 = lean_string_append(x_79, x_82);
lean_dec(x_82);
x_84 = l_Cache_Requests_downloadFiles___lambda__11___closed__24;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_nat_dec_eq(x_55, x_6);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_87 = l_Nat_repr(x_55);
x_88 = l_Cache_Requests_downloadFiles___lambda__4___closed__6;
x_89 = lean_string_append(x_88, x_87);
lean_dec(x_87);
x_90 = l_Cache_Requests_downloadFiles___lambda__4___closed__7;
x_91 = lean_string_append(x_89, x_90);
x_92 = lean_string_append(x_85, x_91);
lean_dec(x_91);
x_93 = lean_box(0);
x_94 = l_Cache_Requests_downloadFiles___lambda__10(x_57, x_92, x_93, x_53);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_55);
x_95 = lean_box(0);
x_96 = l_Cache_Requests_downloadFiles___lambda__10(x_57, x_85, x_95, x_53);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_13);
lean_dec(x_4);
x_97 = !lean_is_exclusive(x_49);
if (x_97 == 0)
{
return x_49;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_49, 0);
x_99 = lean_ctor_get(x_49, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_49);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_13);
lean_dec(x_4);
x_101 = !lean_is_exclusive(x_40);
if (x_101 == 0)
{
return x_40;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_40, 0);
x_103 = lean_ctor_get(x_40, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_40);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_105 = !lean_is_exclusive(x_18);
if (x_105 == 0)
{
return x_18;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_18, 0);
x_107 = lean_ctor_get(x_18, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_18);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_11);
if (x_109 == 0)
{
return x_11;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_11, 0);
x_111 = lean_ctor_get(x_11, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_11);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (x_2 == 0)
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = 0;
x_6 = l_Cache_IO_HashMap_filterExists(x_1, x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Cache_Requests_downloadFiles___lambda__11(x_3, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Cache_Requests_downloadFiles___lambda__11(x_3, x_1, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Cache_Requests_downloadFiles___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_downloadFiles___spec__3(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Cache_Requests_downloadFiles___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Cache_Requests_downloadFiles___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Cache_Requests_downloadFiles___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Cache_Requests_downloadFiles___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Cache_Requests_downloadFiles___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Cache_Requests_downloadFiles___lambda__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Cache_Requests_downloadFiles___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Cache_Requests_downloadFiles___lambda__10(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Cache_Requests_downloadFiles___lambda__11(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_downloadFiles___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Cache_Requests_downloadFiles(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_checkForToolchainMismatch___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_checkForToolchainMismatch___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = lean_io_exit(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_1, x_6, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean-toolchain", 14);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_IO_mathlibDepPath;
x_2 = l_Cache_Requests_checkForToolchainMismatch___closed__1;
x_3 = l_System_FilePath_join(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Cache_Requests_checkForToolchainMismatch___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Dependency Mathlib uses a different lean-toolchain", 50);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  Project uses ", 15);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  Mathlib uses ", 15);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nThe cache will not work unless your project's toolchain matches Mathlib's toolchain", 84);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("This can be achieved by copying the contents of the file `", 58);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_checkForToolchainMismatch___closed__8;
x_2 = l_Cache_Requests_checkForToolchainMismatch___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`\ninto the `lean-toolchain` file at the root directory of your project", 70);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_checkForToolchainMismatch___closed__9;
x_2 = l_Cache_Requests_checkForToolchainMismatch___closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("You can use `cp ", 16);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_checkForToolchainMismatch___closed__12;
x_2 = l_Cache_Requests_checkForToolchainMismatch___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ./lean-toolchain`", 18);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_checkForToolchainMismatch___closed__13;
x_2 = l_Cache_Requests_checkForToolchainMismatch___closed__14;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("On powershell you can use `cp ", 30);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_checkForToolchainMismatch___closed__16;
x_2 = l_Cache_Requests_checkForToolchainMismatch___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_checkForToolchainMismatch___closed__17;
x_2 = l_Cache_Requests_checkForToolchainMismatch___closed__14;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("On Windows CMD you can use `copy ", 33);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_checkForToolchainMismatch___closed__19;
x_2 = l_Cache_Requests_checkForToolchainMismatch___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" lean-toolchain`", 16);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_checkForToolchainMismatch___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_checkForToolchainMismatch___closed__20;
x_2 = l_Cache_Requests_checkForToolchainMismatch___closed__21;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_checkForToolchainMismatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Cache_Requests_checkForToolchainMismatch___closed__1;
x_3 = l_IO_FS_readFile(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Cache_Requests_checkForToolchainMismatch___closed__2;
x_7 = l_IO_FS_readFile(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Cache_Requests_checkForToolchainMismatch___closed__3;
x_11 = l_String_trim(x_8);
lean_dec(x_8);
x_12 = l_String_trim(x_4);
lean_dec(x_4);
x_13 = lean_string_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Cache_Requests_checkForToolchainMismatch___closed__4;
x_15 = l_IO_println___at_Lean_instEval___spec__1(x_14, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Cache_Requests_checkForToolchainMismatch___closed__5;
x_18 = lean_string_append(x_17, x_12);
lean_dec(x_12);
x_19 = l_Cache_Requests_mkFileURL___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_IO_println___at_Lean_instEval___spec__1(x_20, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Cache_Requests_checkForToolchainMismatch___closed__6;
x_24 = lean_string_append(x_23, x_11);
lean_dec(x_11);
x_25 = lean_string_append(x_24, x_19);
x_26 = l_IO_println___at_Lean_instEval___spec__1(x_25, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Cache_Requests_checkForToolchainMismatch___closed__7;
x_29 = l_IO_println___at_Lean_instEval___spec__1(x_28, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Cache_Requests_checkForToolchainMismatch___closed__11;
x_32 = l_IO_println___at_Lean_instEval___spec__1(x_31, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_System_Platform_isWindows;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Cache_Requests_checkForToolchainMismatch___closed__15;
x_36 = l_IO_println___at_Lean_instEval___spec__1(x_35, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Cache_Requests_checkForToolchainMismatch___lambda__2(x_10, x_37, x_38);
lean_dec(x_37);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Cache_Requests_checkForToolchainMismatch___closed__18;
x_45 = l_IO_println___at_Lean_instEval___spec__1(x_44, x_33);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Cache_Requests_checkForToolchainMismatch___closed__22;
x_48 = l_IO_println___at_Lean_instEval___spec__1(x_47, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Cache_Requests_checkForToolchainMismatch___lambda__2(x_10, x_49, x_50);
lean_dec(x_49);
return x_51;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_45);
if (x_56 == 0)
{
return x_45;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_45, 0);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_45);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_32);
if (x_60 == 0)
{
return x_32;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_32, 0);
x_62 = lean_ctor_get(x_32, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_32);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_29);
if (x_64 == 0)
{
return x_29;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_29, 0);
x_66 = lean_ctor_get(x_29, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_29);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_26);
if (x_68 == 0)
{
return x_26;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_26, 0);
x_70 = lean_ctor_get(x_26, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_26);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_11);
x_72 = !lean_is_exclusive(x_21);
if (x_72 == 0)
{
return x_21;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_21, 0);
x_74 = lean_ctor_get(x_21, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_21);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_12);
lean_dec(x_11);
x_76 = !lean_is_exclusive(x_15);
if (x_76 == 0)
{
return x_15;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_15, 0);
x_78 = lean_ctor_get(x_15, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_15);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_12);
lean_dec(x_11);
x_80 = lean_box(0);
x_81 = lean_apply_2(x_10, x_80, x_9);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_4);
x_82 = !lean_is_exclusive(x_7);
if (x_82 == 0)
{
return x_7;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_7, 0);
x_84 = lean_ctor_get(x_7, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_7);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_3);
if (x_86 == 0)
{
return x_3;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_3, 0);
x_88 = lean_ctor_get(x_3, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_3);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_checkForToolchainMismatch___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Cache_Requests_checkForToolchainMismatch___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_checkForToolchainMismatch___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Cache_Requests_checkForToolchainMismatch___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_getFiles___lambda__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Cache_Requests_downloadFiles(x_1, x_2, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
if (x_4 == 0)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l_Cache_IO_unpackCache(x_1, x_5, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_getFiles(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Cache_IO_isMathlibRoot(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Cache_Requests_checkForToolchainMismatch(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Cache_Requests_getFiles___lambda__1(x_1, x_2, x_4, x_5, x_3, x_12, x_13);
lean_dec(x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_box(0);
x_21 = l_Cache_Requests_getFiles___lambda__1(x_1, x_2, x_4, x_5, x_3, x_20, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_getFiles___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Cache_Requests_getFiles___lambda__1(x_1, x_8, x_9, x_10, x_11, x_6, x_7);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_getFiles___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Cache_Requests_getFiles(x_1, x_7, x_8, x_9, x_10, x_6);
return x_11;
}
}
static lean_object* _init_l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-T ", 3);
return x_1;
}
}
static lean_object* _init_l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nurl = ", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_List_reverse___rarg(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = l_Cache_Requests_mkFileURL(x_8, x_10, x_4);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__4;
x_15 = l_System_FilePath_join(x_14, x_8);
x_16 = l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_12);
lean_dec(x_12);
x_21 = l_Cache_Requests_mkFileURL___closed__1;
x_22 = lean_string_append(x_20, x_21);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_22);
{
lean_object* _tmp_1 = x_9;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_3 = x_13;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
lean_inc(x_1);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = l_Cache_Requests_mkFileURL(x_24, x_26, x_4);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__4;
x_31 = l_System_FilePath_join(x_30, x_24);
x_32 = l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_28);
lean_dec(x_28);
x_37 = l_Cache_Requests_mkFileURL___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
x_2 = x_25;
x_3 = x_39;
x_4 = x_29;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_mkPutConfigContent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_array_data(x_1);
x_5 = lean_box(0);
x_6 = l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1(x_2, x_4, x_5, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__5;
x_10 = l_String_intercalate(x_9, x_8);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__5;
x_14 = l_String_intercalate(x_13, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_putFiles___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Cache_IO_CURLCFG;
x_4 = lean_io_remove_file(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("No files to upload", 18);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Attempting to upload ", 21);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Cache_Requests_putFiles___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-X", 2);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_downloadFiles___lambda__11___closed__5;
x_2 = l_Cache_Requests_putFiles___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PUT", 3);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__5;
x_2 = l_Cache_Requests_putFiles___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-H", 2);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__7;
x_2 = l_Cache_Requests_putFiles___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x-ms-blob-type: BlockBlob", 25);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__9;
x_2 = l_Cache_Requests_putFiles___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__11;
x_2 = l_Cache_Requests_putFiles___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("If-None-Match: *", 16);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__12;
x_2 = l_Cache_Requests_putFiles___closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__14;
x_2 = l_Cache_Requests_downloadFiles___lambda__11___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-K", 2);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__15;
x_2 = l_Cache_Requests_putFiles___closed__16;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__17;
x_2 = l_Cache_IO_CURLCFG;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__19;
x_2 = l_Cache_Requests_putFiles___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__20;
x_2 = l_Cache_Requests_putFiles___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__21;
x_2 = l_Cache_Requests_putFiles___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__22;
x_2 = l_Cache_Requests_putFiles___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__23;
x_2 = l_Cache_Requests_downloadFiles___lambda__11___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__24;
x_2 = l_Cache_Requests_putFiles___closed__16;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_putFiles___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_putFiles___closed__25;
x_2 = l_Cache_IO_CURLCFG;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_putFiles(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_8 = l_Cache_Requests_putFiles___closed__1;
x_9 = l_IO_println___at_Lean_instEval___spec__1(x_8, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Cache_Requests_mkPutConfigContent(x_1, x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Cache_IO_CURLCFG;
x_14 = l_IO_FS_writeFile(x_13, x_11, x_12);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Nat_repr(x_5);
x_17 = l_Cache_Requests_putFiles___closed__2;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Cache_Requests_downloadFiles___lambda__11___closed__3;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_IO_println___at_Lean_instEval___spec__1(x_20, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Cache_Requests_putFiles___closed__3;
if (x_2 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Cache_Requests_putFiles___closed__18;
x_25 = 1;
x_26 = l_Cache_IO_runCurl(x_24, x_25, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = lean_apply_2(x_23, x_28, x_27);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = l_Cache_Requests_putFiles___closed__26;
x_35 = 1;
x_36 = l_Cache_IO_runCurl(x_34, x_35, x_22);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = lean_apply_2(x_23, x_38, x_37);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_21);
if (x_44 == 0)
{
return x_21;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_21, 0);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_21);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
return x_14;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_14, 0);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_14);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_putFiles___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Cache_Requests_putFiles___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_putFiles___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Cache_Requests_putFiles(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Cache_Requests_isGitStatusClean___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Cache_Requests_isGitStatusClean___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("status", 6);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_isGitStatusClean___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_isGitStatusClean___closed__1;
x_2 = l_Cache_Requests_isGitStatusClean___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_isGitStatusClean___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--porcelain", 11);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_isGitStatusClean___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_isGitStatusClean___closed__3;
x_2 = l_Cache_Requests_isGitStatusClean___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_isGitStatusClean___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("git", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_isGitStatusClean(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Cache_Requests_isGitStatusClean___closed__6;
x_3 = l_Cache_Requests_isGitStatusClean___closed__5;
x_4 = 1;
x_5 = l_Cache_IO_runCmd(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_String_isEmpty(x_7);
lean_dec(x_7);
x_9 = lean_box(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = l_String_isEmpty(x_10);
lean_dec(x_10);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Cache_Requests_getGitCommitHash___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rev-parse", 9);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_getGitCommitHash___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_isGitStatusClean___closed__1;
x_2 = l_Cache_Requests_getGitCommitHash___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_getGitCommitHash___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HEAD", 4);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_getGitCommitHash___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_getGitCommitHash___closed__2;
x_2 = l_Cache_Requests_getGitCommitHash___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_getGitCommitHash(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Cache_Requests_isGitStatusClean___closed__6;
x_3 = l_Cache_Requests_getGitCommitHash___closed__4;
x_4 = 1;
x_5 = l_Cache_IO_runCmd(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_String_trimRight(x_7);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_String_trimRight(x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Cache_Requests_commit___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 3);
x_6 = l_Lean_RBNode_revFold___at_Cache_Requests_commit___spec__2(x_1, x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_3;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___at_Cache_Requests_commit___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_RBNode_revFold___at_Cache_Requests_commit___spec__2(x_2, x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Cache_Requests_commit___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_8 = lean_uint64_to_nat(x_7);
x_9 = l_Nat_repr(x_8);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_9);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_unbox_uint64(x_11);
lean_dec(x_11);
x_14 = lean_uint64_to_nat(x_13);
x_15 = l_Nat_repr(x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
x_1 = x_12;
x_2 = x_16;
goto _start;
}
}
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("/c/", 3);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_mkFileURL___closed__2;
x_2 = l_Cache_Requests_commit___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-T", 2);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_commit___closed__3;
x_2 = l_Cache_Requests_commit___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_commit___closed__6;
x_2 = l_Cache_Requests_putFiles___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_commit___closed__7;
x_2 = l_Cache_Requests_putFiles___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_commit___closed__8;
x_2 = l_Cache_Requests_putFiles___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_commit___closed__9;
x_2 = l_Cache_Requests_putFiles___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_commit___closed__10;
x_2 = l_Cache_Requests_putFiles___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_commit___closed__11;
x_2 = l_Cache_Requests_putFiles___closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_commit___closed__13;
x_2 = l_Cache_Requests_putFiles___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_commit___closed__14;
x_2 = l_Cache_Requests_putFiles___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_commit___closed__15;
x_2 = l_Cache_Requests_putFiles___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_commit___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_commit___closed__16;
x_2 = l_Cache_Requests_putFiles___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_commit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Cache_Requests_getGitCommitHash(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__4;
lean_inc(x_6);
x_9 = l_System_FilePath_join(x_8, x_6);
x_10 = l_Cache_IO_mkDir(x_8, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Cache_IO_HashMap_hashes(x_1);
x_13 = l_Lean_RBTree_toList___at_Cache_Requests_commit___spec__1(x_12);
x_14 = lean_box(0);
x_15 = l_List_mapTR_loop___at_Cache_Requests_commit___spec__3(x_13, x_14);
x_16 = l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__5;
x_17 = l_String_intercalate(x_16, x_15);
x_18 = lean_string_append(x_17, x_16);
x_19 = l_IO_FS_writeFile(x_9, x_18, x_11);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Cache_Requests_commit___closed__2;
x_22 = lean_string_append(x_21, x_6);
lean_dec(x_6);
x_23 = l_Cache_Requests_mkFileURL___closed__5;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_3);
x_26 = l_Cache_Requests_mkFileURL___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Cache_Requests_commit___closed__5;
lean_inc(x_9);
x_29 = lean_array_push(x_28, x_9);
x_30 = lean_array_push(x_29, x_27);
if (x_2 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_31 = l_Cache_Requests_commit___closed__12;
x_32 = l_Array_append___rarg(x_31, x_30);
x_33 = 1;
x_34 = l_Cache_IO_runCurl(x_32, x_33, x_20);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_io_remove_file(x_9, x_35);
lean_dec(x_9);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_9);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_41 = l_Cache_Requests_commit___closed__17;
x_42 = l_Array_append___rarg(x_41, x_30);
x_43 = 1;
x_44 = l_Cache_IO_runCurl(x_42, x_43, x_20);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_io_remove_file(x_9, x_45);
lean_dec(x_9);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_9);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_9);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_19);
if (x_51 == 0)
{
return x_19;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_19, 0);
x_53 = lean_ctor_get(x_19, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_19);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_10);
if (x_55 == 0)
{
return x_10;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_10, 0);
x_57 = lean_ctor_get(x_10, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_10);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_5);
if (x_59 == 0)
{
return x_5;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_5, 0);
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_5);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at_Cache_Requests_commit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_revFold___at_Cache_Requests_commit___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_commit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Cache_Requests_commit(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Cache_Requests_QueryType_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_QueryType_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Cache_Requests_QueryType_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Cache_Requests_QueryType_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Cache_Requests_QueryType_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Cache_Requests_QueryType_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Cache_Requests_QueryType_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Cache_Requests_QueryType_prefix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("&prefix=f/", 10);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_QueryType_prefix___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("&prefix=c/", 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_prefix(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Cache_Requests_QueryType_prefix___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Cache_Requests_QueryType_prefix___closed__2;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Cache_Requests_mkFileURL___closed__1;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_prefix___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Cache_Requests_QueryType_prefix(x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_formatError___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Invalid format for curl return", 30);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_formatError___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Cache_Requests_formatError___rarg___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_formatError___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Cache_Requests_formatError___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_formatError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Cache_Requests_formatError___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Cache_Requests_QueryType_desc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hosted files", 12);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_QueryType_desc___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hosted commits", 14);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_QueryType_desc___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("everything", 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_desc(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Cache_Requests_QueryType_desc___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Cache_Requests_QueryType_desc___closed__2;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Cache_Requests_QueryType_desc___closed__3;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_QueryType_desc___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Cache_Requests_QueryType_desc(x_2);
return x_3;
}
}
static lean_object* _init_l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("</Name>", 7);
return x_1;
}
}
static lean_object* _init_l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<Last-Modified>", 15);
return x_1;
}
}
static lean_object* _init_l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("</Last-Modified>", 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_reverse___rarg(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_19; lean_object* x_20; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_8 = x_1;
} else {
 lean_dec_ref(x_1);
 x_8 = lean_box(0);
}
x_19 = l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__1;
x_20 = l_String_splitOn(x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = l_Cache_Requests_formatError___rarg(x_3);
x_9 = x_21;
goto block_18;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = l_Cache_Requests_formatError___rarg(x_3);
x_9 = x_23;
goto block_18;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__2;
x_28 = l_String_splitOn(x_26, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec(x_25);
x_29 = l_Cache_Requests_formatError___rarg(x_3);
x_9 = x_29;
goto block_18;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_25);
x_31 = l_Cache_Requests_formatError___rarg(x_3);
x_9 = x_31;
goto block_18;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__3;
x_35 = l_String_splitOn(x_33, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec(x_25);
x_36 = l_Cache_Requests_formatError___rarg(x_3);
x_9 = x_36;
goto block_18;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_25);
x_38 = l_Cache_Requests_formatError___rarg(x_3);
x_9 = x_38;
goto block_18;
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_25);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_3);
x_9 = x_42;
goto block_18;
}
else
{
lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_25);
x_43 = l_Cache_Requests_formatError___rarg(x_3);
x_9 = x_43;
goto block_18;
}
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
x_44 = l_Cache_Requests_formatError___rarg(x_3);
x_9 = x_44;
goto block_18;
}
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
x_45 = l_Cache_Requests_formatError___rarg(x_3);
x_9 = x_45;
goto block_18;
}
}
}
block_18:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
if (lean_is_scalar(x_8)) {
 x_12 = lean_alloc_ctor(1, 2, 0);
} else {
 x_12 = x_8;
}
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_7;
x_2 = x_12;
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
}
static lean_object* _init_l_Cache_Requests_getFilesInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Downloading info list of ", 25);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_getFilesInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\?comp=list&restype=container", 28);
return x_1;
}
}
static lean_object* _init_l_Cache_Requests_getFilesInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_mkFileURL___closed__2;
x_2 = l_Cache_Requests_getFilesInfo___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_getFilesInfo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_commit___closed__3;
x_2 = l_Cache_Requests_putFiles___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_getFilesInfo___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cache_Requests_getFilesInfo___closed__4;
x_2 = l_Cache_Requests_downloadFiles___lambda__11___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Cache_Requests_getFilesInfo___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<Name>", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_getFilesInfo(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Cache_Requests_QueryType_desc(x_1);
x_4 = l_Cache_Requests_getFilesInfo___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Cache_Requests_mkFileURL___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_IO_println___at_Lean_instEval___spec__1(x_7, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Cache_Requests_QueryType_prefix(x_1);
x_11 = l_Cache_Requests_getFilesInfo___closed__3;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = lean_string_append(x_12, x_6);
x_14 = l_Cache_Requests_getFilesInfo___closed__5;
x_15 = lean_array_push(x_14, x_13);
x_16 = 1;
x_17 = l_Cache_IO_runCurl(x_15, x_16, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Cache_Requests_getFilesInfo___closed__6;
x_22 = l_String_splitOn(x_19, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_free_object(x_17);
x_23 = l_Cache_Requests_formatError___rarg(x_20);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_box(0);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_17);
x_26 = lean_box(0);
x_27 = l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1(x_24, x_26, x_20);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = l_Cache_Requests_getFilesInfo___closed__6;
x_31 = l_String_splitOn(x_28, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = l_Cache_Requests_formatError___rarg(x_29);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1(x_33, x_36, x_29);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Cache_Requests_getFilesInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Cache_Requests_getFilesInfo(x_3, x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_Parser(uint8_t builtin, lean_object*);
lean_object* initialize_Cache_Hashing(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Cache_Requests(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Parser(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Cache_Hashing(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Cache_Requests_URL___closed__1 = _init_l_Cache_Requests_URL___closed__1();
lean_mark_persistent(l_Cache_Requests_URL___closed__1);
l_Cache_Requests_URL = _init_l_Cache_Requests_URL();
lean_mark_persistent(l_Cache_Requests_URL);
l_Cache_Requests_mkFileURL___closed__1 = _init_l_Cache_Requests_mkFileURL___closed__1();
lean_mark_persistent(l_Cache_Requests_mkFileURL___closed__1);
l_Cache_Requests_mkFileURL___closed__2 = _init_l_Cache_Requests_mkFileURL___closed__2();
lean_mark_persistent(l_Cache_Requests_mkFileURL___closed__2);
l_Cache_Requests_mkFileURL___closed__3 = _init_l_Cache_Requests_mkFileURL___closed__3();
lean_mark_persistent(l_Cache_Requests_mkFileURL___closed__3);
l_Cache_Requests_mkFileURL___closed__4 = _init_l_Cache_Requests_mkFileURL___closed__4();
lean_mark_persistent(l_Cache_Requests_mkFileURL___closed__4);
l_Cache_Requests_mkFileURL___closed__5 = _init_l_Cache_Requests_mkFileURL___closed__5();
lean_mark_persistent(l_Cache_Requests_mkFileURL___closed__5);
l_Lean_HashMap_toArray___at_Cache_Requests_mkGetConfigContent___spec__1___closed__1 = _init_l_Lean_HashMap_toArray___at_Cache_Requests_mkGetConfigContent___spec__1___closed__1();
lean_mark_persistent(l_Lean_HashMap_toArray___at_Cache_Requests_mkGetConfigContent___spec__1___closed__1);
l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__1 = _init_l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__1);
l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__2 = _init_l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__2();
lean_mark_persistent(l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__2);
l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__3 = _init_l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__3();
lean_mark_persistent(l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___lambda__1___closed__3);
l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___closed__1 = _init_l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Cache_Requests_mkGetConfigContent___spec__4___closed__1);
l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__1);
l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__2);
l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__3);
l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__4 = _init_l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__4);
l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__5 = _init_l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__5();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Cache_Requests_mkGetConfigContent___spec__5___closed__5);
l_Cache_Requests_downloadFile___closed__1 = _init_l_Cache_Requests_downloadFile___closed__1();
lean_mark_persistent(l_Cache_Requests_downloadFile___closed__1);
l_Cache_Requests_downloadFile___closed__2 = _init_l_Cache_Requests_downloadFile___closed__2();
lean_mark_persistent(l_Cache_Requests_downloadFile___closed__2);
l_Cache_Requests_downloadFile___closed__3 = _init_l_Cache_Requests_downloadFile___closed__3();
lean_mark_persistent(l_Cache_Requests_downloadFile___closed__3);
l_Cache_Requests_downloadFile___closed__4 = _init_l_Cache_Requests_downloadFile___closed__4();
lean_mark_persistent(l_Cache_Requests_downloadFile___closed__4);
l_Cache_Requests_downloadFile___closed__5 = _init_l_Cache_Requests_downloadFile___closed__5();
lean_mark_persistent(l_Cache_Requests_downloadFile___closed__5);
l_Cache_Requests_downloadFiles___lambda__1___closed__1 = _init_l_Cache_Requests_downloadFiles___lambda__1___closed__1();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__1___closed__1);
l_Cache_Requests_downloadFiles___lambda__4___closed__1 = _init_l_Cache_Requests_downloadFiles___lambda__4___closed__1();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__4___closed__1);
l_Cache_Requests_downloadFiles___lambda__4___closed__2 = _init_l_Cache_Requests_downloadFiles___lambda__4___closed__2();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__4___closed__2);
l_Cache_Requests_downloadFiles___lambda__4___closed__3 = _init_l_Cache_Requests_downloadFiles___lambda__4___closed__3();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__4___closed__3);
l_Cache_Requests_downloadFiles___lambda__4___closed__4 = _init_l_Cache_Requests_downloadFiles___lambda__4___closed__4();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__4___closed__4);
l_Cache_Requests_downloadFiles___lambda__4___closed__5 = _init_l_Cache_Requests_downloadFiles___lambda__4___closed__5();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__4___closed__5);
l_Cache_Requests_downloadFiles___lambda__4___closed__6 = _init_l_Cache_Requests_downloadFiles___lambda__4___closed__6();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__4___closed__6);
l_Cache_Requests_downloadFiles___lambda__4___closed__7 = _init_l_Cache_Requests_downloadFiles___lambda__4___closed__7();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__4___closed__7);
l_Cache_Requests_downloadFiles___lambda__5___closed__1 = _init_l_Cache_Requests_downloadFiles___lambda__5___closed__1();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__5___closed__1);
l_Cache_Requests_downloadFiles___lambda__7___closed__1 = _init_l_Cache_Requests_downloadFiles___lambda__7___closed__1();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__7___closed__1);
l_Cache_Requests_downloadFiles___lambda__7___closed__2 = _init_l_Cache_Requests_downloadFiles___lambda__7___closed__2();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__7___closed__2);
l_Cache_Requests_downloadFiles___lambda__7___closed__3 = _init_l_Cache_Requests_downloadFiles___lambda__7___closed__3();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__7___closed__3);
l_Cache_Requests_downloadFiles___lambda__9___closed__1 = _init_l_Cache_Requests_downloadFiles___lambda__9___closed__1();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__9___closed__1);
l_Cache_Requests_downloadFiles___lambda__9___closed__2 = _init_l_Cache_Requests_downloadFiles___lambda__9___closed__2();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__9___closed__2);
l_Cache_Requests_downloadFiles___lambda__9___closed__3 = _init_l_Cache_Requests_downloadFiles___lambda__9___closed__3();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__9___closed__3);
l_Cache_Requests_downloadFiles___lambda__11___closed__1 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__1();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__1);
l_Cache_Requests_downloadFiles___lambda__11___closed__2 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__2();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__2);
l_Cache_Requests_downloadFiles___lambda__11___closed__3 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__3();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__3);
l_Cache_Requests_downloadFiles___lambda__11___closed__4 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__4();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__4);
l_Cache_Requests_downloadFiles___lambda__11___closed__5 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__5();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__5);
l_Cache_Requests_downloadFiles___lambda__11___closed__6 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__6();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__6);
l_Cache_Requests_downloadFiles___lambda__11___closed__7 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__7();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__7);
l_Cache_Requests_downloadFiles___lambda__11___closed__8 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__8();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__8);
l_Cache_Requests_downloadFiles___lambda__11___closed__9 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__9();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__9);
l_Cache_Requests_downloadFiles___lambda__11___closed__10 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__10();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__10);
l_Cache_Requests_downloadFiles___lambda__11___closed__11 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__11();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__11);
l_Cache_Requests_downloadFiles___lambda__11___closed__12 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__12();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__12);
l_Cache_Requests_downloadFiles___lambda__11___closed__13 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__13();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__13);
l_Cache_Requests_downloadFiles___lambda__11___closed__14 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__14();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__14);
l_Cache_Requests_downloadFiles___lambda__11___closed__15 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__15();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__15);
l_Cache_Requests_downloadFiles___lambda__11___closed__16 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__16();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__16);
l_Cache_Requests_downloadFiles___lambda__11___closed__17 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__17();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__17);
l_Cache_Requests_downloadFiles___lambda__11___closed__18 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__18();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__18);
l_Cache_Requests_downloadFiles___lambda__11___closed__19 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__19();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__19);
l_Cache_Requests_downloadFiles___lambda__11___closed__20 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__20();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__20);
l_Cache_Requests_downloadFiles___lambda__11___closed__21 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__21();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__21);
l_Cache_Requests_downloadFiles___lambda__11___closed__22 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__22();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__22);
l_Cache_Requests_downloadFiles___lambda__11___closed__23 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__23();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__23);
l_Cache_Requests_downloadFiles___lambda__11___closed__24 = _init_l_Cache_Requests_downloadFiles___lambda__11___closed__24();
lean_mark_persistent(l_Cache_Requests_downloadFiles___lambda__11___closed__24);
l_Cache_Requests_checkForToolchainMismatch___closed__1 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__1();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__1);
l_Cache_Requests_checkForToolchainMismatch___closed__2 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__2();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__2);
l_Cache_Requests_checkForToolchainMismatch___closed__3 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__3();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__3);
l_Cache_Requests_checkForToolchainMismatch___closed__4 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__4();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__4);
l_Cache_Requests_checkForToolchainMismatch___closed__5 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__5();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__5);
l_Cache_Requests_checkForToolchainMismatch___closed__6 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__6();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__6);
l_Cache_Requests_checkForToolchainMismatch___closed__7 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__7();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__7);
l_Cache_Requests_checkForToolchainMismatch___closed__8 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__8();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__8);
l_Cache_Requests_checkForToolchainMismatch___closed__9 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__9();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__9);
l_Cache_Requests_checkForToolchainMismatch___closed__10 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__10();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__10);
l_Cache_Requests_checkForToolchainMismatch___closed__11 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__11();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__11);
l_Cache_Requests_checkForToolchainMismatch___closed__12 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__12();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__12);
l_Cache_Requests_checkForToolchainMismatch___closed__13 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__13();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__13);
l_Cache_Requests_checkForToolchainMismatch___closed__14 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__14();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__14);
l_Cache_Requests_checkForToolchainMismatch___closed__15 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__15();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__15);
l_Cache_Requests_checkForToolchainMismatch___closed__16 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__16();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__16);
l_Cache_Requests_checkForToolchainMismatch___closed__17 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__17();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__17);
l_Cache_Requests_checkForToolchainMismatch___closed__18 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__18();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__18);
l_Cache_Requests_checkForToolchainMismatch___closed__19 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__19();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__19);
l_Cache_Requests_checkForToolchainMismatch___closed__20 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__20();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__20);
l_Cache_Requests_checkForToolchainMismatch___closed__21 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__21();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__21);
l_Cache_Requests_checkForToolchainMismatch___closed__22 = _init_l_Cache_Requests_checkForToolchainMismatch___closed__22();
lean_mark_persistent(l_Cache_Requests_checkForToolchainMismatch___closed__22);
l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__1 = _init_l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__1();
lean_mark_persistent(l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__1);
l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__2 = _init_l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__2();
lean_mark_persistent(l_List_mapM_loop___at_Cache_Requests_mkPutConfigContent___spec__1___closed__2);
l_Cache_Requests_putFiles___closed__1 = _init_l_Cache_Requests_putFiles___closed__1();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__1);
l_Cache_Requests_putFiles___closed__2 = _init_l_Cache_Requests_putFiles___closed__2();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__2);
l_Cache_Requests_putFiles___closed__3 = _init_l_Cache_Requests_putFiles___closed__3();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__3);
l_Cache_Requests_putFiles___closed__4 = _init_l_Cache_Requests_putFiles___closed__4();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__4);
l_Cache_Requests_putFiles___closed__5 = _init_l_Cache_Requests_putFiles___closed__5();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__5);
l_Cache_Requests_putFiles___closed__6 = _init_l_Cache_Requests_putFiles___closed__6();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__6);
l_Cache_Requests_putFiles___closed__7 = _init_l_Cache_Requests_putFiles___closed__7();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__7);
l_Cache_Requests_putFiles___closed__8 = _init_l_Cache_Requests_putFiles___closed__8();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__8);
l_Cache_Requests_putFiles___closed__9 = _init_l_Cache_Requests_putFiles___closed__9();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__9);
l_Cache_Requests_putFiles___closed__10 = _init_l_Cache_Requests_putFiles___closed__10();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__10);
l_Cache_Requests_putFiles___closed__11 = _init_l_Cache_Requests_putFiles___closed__11();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__11);
l_Cache_Requests_putFiles___closed__12 = _init_l_Cache_Requests_putFiles___closed__12();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__12);
l_Cache_Requests_putFiles___closed__13 = _init_l_Cache_Requests_putFiles___closed__13();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__13);
l_Cache_Requests_putFiles___closed__14 = _init_l_Cache_Requests_putFiles___closed__14();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__14);
l_Cache_Requests_putFiles___closed__15 = _init_l_Cache_Requests_putFiles___closed__15();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__15);
l_Cache_Requests_putFiles___closed__16 = _init_l_Cache_Requests_putFiles___closed__16();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__16);
l_Cache_Requests_putFiles___closed__17 = _init_l_Cache_Requests_putFiles___closed__17();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__17);
l_Cache_Requests_putFiles___closed__18 = _init_l_Cache_Requests_putFiles___closed__18();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__18);
l_Cache_Requests_putFiles___closed__19 = _init_l_Cache_Requests_putFiles___closed__19();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__19);
l_Cache_Requests_putFiles___closed__20 = _init_l_Cache_Requests_putFiles___closed__20();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__20);
l_Cache_Requests_putFiles___closed__21 = _init_l_Cache_Requests_putFiles___closed__21();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__21);
l_Cache_Requests_putFiles___closed__22 = _init_l_Cache_Requests_putFiles___closed__22();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__22);
l_Cache_Requests_putFiles___closed__23 = _init_l_Cache_Requests_putFiles___closed__23();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__23);
l_Cache_Requests_putFiles___closed__24 = _init_l_Cache_Requests_putFiles___closed__24();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__24);
l_Cache_Requests_putFiles___closed__25 = _init_l_Cache_Requests_putFiles___closed__25();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__25);
l_Cache_Requests_putFiles___closed__26 = _init_l_Cache_Requests_putFiles___closed__26();
lean_mark_persistent(l_Cache_Requests_putFiles___closed__26);
l_Cache_Requests_isGitStatusClean___closed__1 = _init_l_Cache_Requests_isGitStatusClean___closed__1();
lean_mark_persistent(l_Cache_Requests_isGitStatusClean___closed__1);
l_Cache_Requests_isGitStatusClean___closed__2 = _init_l_Cache_Requests_isGitStatusClean___closed__2();
lean_mark_persistent(l_Cache_Requests_isGitStatusClean___closed__2);
l_Cache_Requests_isGitStatusClean___closed__3 = _init_l_Cache_Requests_isGitStatusClean___closed__3();
lean_mark_persistent(l_Cache_Requests_isGitStatusClean___closed__3);
l_Cache_Requests_isGitStatusClean___closed__4 = _init_l_Cache_Requests_isGitStatusClean___closed__4();
lean_mark_persistent(l_Cache_Requests_isGitStatusClean___closed__4);
l_Cache_Requests_isGitStatusClean___closed__5 = _init_l_Cache_Requests_isGitStatusClean___closed__5();
lean_mark_persistent(l_Cache_Requests_isGitStatusClean___closed__5);
l_Cache_Requests_isGitStatusClean___closed__6 = _init_l_Cache_Requests_isGitStatusClean___closed__6();
lean_mark_persistent(l_Cache_Requests_isGitStatusClean___closed__6);
l_Cache_Requests_getGitCommitHash___closed__1 = _init_l_Cache_Requests_getGitCommitHash___closed__1();
lean_mark_persistent(l_Cache_Requests_getGitCommitHash___closed__1);
l_Cache_Requests_getGitCommitHash___closed__2 = _init_l_Cache_Requests_getGitCommitHash___closed__2();
lean_mark_persistent(l_Cache_Requests_getGitCommitHash___closed__2);
l_Cache_Requests_getGitCommitHash___closed__3 = _init_l_Cache_Requests_getGitCommitHash___closed__3();
lean_mark_persistent(l_Cache_Requests_getGitCommitHash___closed__3);
l_Cache_Requests_getGitCommitHash___closed__4 = _init_l_Cache_Requests_getGitCommitHash___closed__4();
lean_mark_persistent(l_Cache_Requests_getGitCommitHash___closed__4);
l_Cache_Requests_commit___closed__1 = _init_l_Cache_Requests_commit___closed__1();
lean_mark_persistent(l_Cache_Requests_commit___closed__1);
l_Cache_Requests_commit___closed__2 = _init_l_Cache_Requests_commit___closed__2();
lean_mark_persistent(l_Cache_Requests_commit___closed__2);
l_Cache_Requests_commit___closed__3 = _init_l_Cache_Requests_commit___closed__3();
lean_mark_persistent(l_Cache_Requests_commit___closed__3);
l_Cache_Requests_commit___closed__4 = _init_l_Cache_Requests_commit___closed__4();
lean_mark_persistent(l_Cache_Requests_commit___closed__4);
l_Cache_Requests_commit___closed__5 = _init_l_Cache_Requests_commit___closed__5();
lean_mark_persistent(l_Cache_Requests_commit___closed__5);
l_Cache_Requests_commit___closed__6 = _init_l_Cache_Requests_commit___closed__6();
lean_mark_persistent(l_Cache_Requests_commit___closed__6);
l_Cache_Requests_commit___closed__7 = _init_l_Cache_Requests_commit___closed__7();
lean_mark_persistent(l_Cache_Requests_commit___closed__7);
l_Cache_Requests_commit___closed__8 = _init_l_Cache_Requests_commit___closed__8();
lean_mark_persistent(l_Cache_Requests_commit___closed__8);
l_Cache_Requests_commit___closed__9 = _init_l_Cache_Requests_commit___closed__9();
lean_mark_persistent(l_Cache_Requests_commit___closed__9);
l_Cache_Requests_commit___closed__10 = _init_l_Cache_Requests_commit___closed__10();
lean_mark_persistent(l_Cache_Requests_commit___closed__10);
l_Cache_Requests_commit___closed__11 = _init_l_Cache_Requests_commit___closed__11();
lean_mark_persistent(l_Cache_Requests_commit___closed__11);
l_Cache_Requests_commit___closed__12 = _init_l_Cache_Requests_commit___closed__12();
lean_mark_persistent(l_Cache_Requests_commit___closed__12);
l_Cache_Requests_commit___closed__13 = _init_l_Cache_Requests_commit___closed__13();
lean_mark_persistent(l_Cache_Requests_commit___closed__13);
l_Cache_Requests_commit___closed__14 = _init_l_Cache_Requests_commit___closed__14();
lean_mark_persistent(l_Cache_Requests_commit___closed__14);
l_Cache_Requests_commit___closed__15 = _init_l_Cache_Requests_commit___closed__15();
lean_mark_persistent(l_Cache_Requests_commit___closed__15);
l_Cache_Requests_commit___closed__16 = _init_l_Cache_Requests_commit___closed__16();
lean_mark_persistent(l_Cache_Requests_commit___closed__16);
l_Cache_Requests_commit___closed__17 = _init_l_Cache_Requests_commit___closed__17();
lean_mark_persistent(l_Cache_Requests_commit___closed__17);
l_Cache_Requests_QueryType_noConfusion___rarg___closed__1 = _init_l_Cache_Requests_QueryType_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Cache_Requests_QueryType_noConfusion___rarg___closed__1);
l_Cache_Requests_QueryType_prefix___closed__1 = _init_l_Cache_Requests_QueryType_prefix___closed__1();
lean_mark_persistent(l_Cache_Requests_QueryType_prefix___closed__1);
l_Cache_Requests_QueryType_prefix___closed__2 = _init_l_Cache_Requests_QueryType_prefix___closed__2();
lean_mark_persistent(l_Cache_Requests_QueryType_prefix___closed__2);
l_Cache_Requests_formatError___rarg___closed__1 = _init_l_Cache_Requests_formatError___rarg___closed__1();
lean_mark_persistent(l_Cache_Requests_formatError___rarg___closed__1);
l_Cache_Requests_formatError___rarg___closed__2 = _init_l_Cache_Requests_formatError___rarg___closed__2();
lean_mark_persistent(l_Cache_Requests_formatError___rarg___closed__2);
l_Cache_Requests_QueryType_desc___closed__1 = _init_l_Cache_Requests_QueryType_desc___closed__1();
lean_mark_persistent(l_Cache_Requests_QueryType_desc___closed__1);
l_Cache_Requests_QueryType_desc___closed__2 = _init_l_Cache_Requests_QueryType_desc___closed__2();
lean_mark_persistent(l_Cache_Requests_QueryType_desc___closed__2);
l_Cache_Requests_QueryType_desc___closed__3 = _init_l_Cache_Requests_QueryType_desc___closed__3();
lean_mark_persistent(l_Cache_Requests_QueryType_desc___closed__3);
l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__1 = _init_l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__1();
lean_mark_persistent(l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__1);
l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__2 = _init_l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__2();
lean_mark_persistent(l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__2);
l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__3 = _init_l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__3();
lean_mark_persistent(l_List_mapM_loop___at_Cache_Requests_getFilesInfo___spec__1___closed__3);
l_Cache_Requests_getFilesInfo___closed__1 = _init_l_Cache_Requests_getFilesInfo___closed__1();
lean_mark_persistent(l_Cache_Requests_getFilesInfo___closed__1);
l_Cache_Requests_getFilesInfo___closed__2 = _init_l_Cache_Requests_getFilesInfo___closed__2();
lean_mark_persistent(l_Cache_Requests_getFilesInfo___closed__2);
l_Cache_Requests_getFilesInfo___closed__3 = _init_l_Cache_Requests_getFilesInfo___closed__3();
lean_mark_persistent(l_Cache_Requests_getFilesInfo___closed__3);
l_Cache_Requests_getFilesInfo___closed__4 = _init_l_Cache_Requests_getFilesInfo___closed__4();
lean_mark_persistent(l_Cache_Requests_getFilesInfo___closed__4);
l_Cache_Requests_getFilesInfo___closed__5 = _init_l_Cache_Requests_getFilesInfo___closed__5();
lean_mark_persistent(l_Cache_Requests_getFilesInfo___closed__5);
l_Cache_Requests_getFilesInfo___closed__6 = _init_l_Cache_Requests_getFilesInfo___closed__6();
lean_mark_persistent(l_Cache_Requests_getFilesInfo___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
