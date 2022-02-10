all:
	agda Div2.agda

clean:
	rm -f *.agdai

html:
	mkdir -p html
	agda --html Div2.agda
	cd html && ln -s Div2.html index.html
