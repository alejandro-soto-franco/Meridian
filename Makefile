# Meridian — RDF/SPARQL export targets.
#
# Targets:
#   make build              Compile the Meridian library.
#   make test               Run the test suite.
#   make export-mathlib     Dump the full Mathlib environment to out/mathlib.ttl
#                           and compute its SHA-256.
#   make validate           Validate out/mathlib.ttl with rdflib + SPARQL queries.
#   make validate-shacl     Same plus SHACL shape validation.
#   make release            Gzip the dump, write a manifest, and stage for upload.
#   make clean              Remove out/ artefacts.

DUMP        := out/mathlib.ttl
DUMP_GZ     := out/mathlib.ttl.gz
MANIFEST    := out/manifest.json
DRIVER      := Drivers/ExportMathlib.lean

.PHONY: build test export-mathlib validate validate-shacl release clean

build:
	lake build Meridian

test:
	lake build TestCore

$(DUMP): $(DRIVER) Meridian/Core/ExportRdf.lean
	@mkdir -p out
	lake env lean $(DRIVER)
	@sha256sum $(DUMP) > $(DUMP).sha256
	@ls -lh $(DUMP)

export-mathlib: $(DUMP)

validate: $(DUMP)
	uv run --quiet --with rdflib scripts/validate-dump.py $(DUMP)

validate-shacl: $(DUMP)
	uv run --quiet --with rdflib --with pyshacl scripts/validate-dump.py --shacl $(DUMP)

$(DUMP_GZ): $(DUMP)
	gzip -k -9 -f $(DUMP)
	@ls -lh $(DUMP_GZ)

$(MANIFEST): $(DUMP_GZ)
	@./scripts/release-dump.sh $(DUMP) $(MANIFEST)

release: $(DUMP_GZ) $(MANIFEST)
	@echo "Release artefacts staged in out/."
	@echo "  $(DUMP)         — uncompressed Turtle"
	@echo "  $(DUMP_GZ)      — gzip -9 compressed"
	@echo "  $(DUMP).sha256  — SHA-256 of uncompressed dump"
	@echo "  $(MANIFEST)     — release manifest (JSON)"
	@echo
	@echo "To upload as a GitHub release asset, run:"
	@echo "  gh release create vX.Y.Z $(DUMP_GZ) $(DUMP).sha256 $(MANIFEST) \\"
	@echo "    --title 'Mathlib RDF dump (Meridian vX.Y.Z)' --notes-file CHANGELOG.md"

clean:
	rm -rf out/
