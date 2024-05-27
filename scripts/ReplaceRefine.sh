mkPythonFile () {
  local pyScript=scripts/addQuestionMarks.py
  local buildReport=pasteBuild.lk
  grep -v '^add_question_mark' "${pyScript}"
  sed '
    /^info/d
    s=\.=/=g
    s|ℹ .* \(.*\)|input_file = '"'"'\1.lean'"'"'\noutput_file = '"'"'\1.lean1'"'"'\nlines_columns = |
    s=(false, ⟨=(0, =g
    s=(true, ⟨=(1, =g
    s=⟩==g' "${buildReport}" |
  sed -z '
    s=]\n#\[=, =g
    s=\n#\[=[=g
    s=]\n=]\nadd_question_mark(input_file, output_file, lines_columns)\n\nos.rename(output_file, input_file)\n\n=g'
}
