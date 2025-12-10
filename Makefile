.PHONY: validator doc

validator: .first-run-done
	lake build Validator

# https://leanprover-community.github.io/install/project.html#creating-a-lean-project
.first-run-done:
	lake exe cache get
	touch .first-run-done

doc:
	cd docbuild && lake -Kenv=dev build Validator:docs

show-doc: doc
	(sleep 2 && flatpak run io.gitlab.librewolf-community http://127.0.0.1:8000/Validator.html) &
	cd docbuild/.lake/build/doc && python -m http.server --bind 127.0.0.1

clean:
	rm -rf .first-run-done lake-packages .lake build lakefile.olean

dependencies.svg:
	python dependencies.py
