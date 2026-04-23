/-
Smoke test for #discr_tree_export. Runs the command against the current
environment (which has only a handful of declarations available at this
preamble) and writes to /tmp.
-/
import Meridian.Analysis.DiscrTreeExport

#discr_tree_export "/tmp/meridian_discr_tree_test.json"
