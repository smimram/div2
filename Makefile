all clean:
	$(MAKE) -C agda $@

ci:
	git ci . -m "Update."
	git push
