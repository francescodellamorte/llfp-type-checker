CC := ocamlbuild
SR := src
SRC := sourcefiles
LIB := library
CFLAGS := -use-ocamlfind -tag thread -I $(SR)

.PHONY: all mproper

all: main

main:
	$(CC) $(CFLAGS) $(SR)/main_object.native
	mv main_object.native type_checking
	$(CC) $(CFLAGS) $(SR)/main_type.native
	mv main_type.native kind_checking
	$(CC) $(CFLAGS) $(SR)/main_kind.native
	mv main_kind.native is_kind
	
clean:
	$(CC) -clean

