@dnl = internal constant [4 x i8] c"%d\0A\00"
@d   = internal constant [3 x i8] c"%d\00"
@err = internal constant [15 x i8] c"runtime error\0A\00"

@__stdinp = external global i32*, align 8

declare i64 @strlen(i8* noundef) #3
declare noalias i8* @malloc(i64 noundef) #4
declare i8* @strcpy(i8* noundef, i8* noundef) #4
declare i8* @strcat(i8* noundef, i8* noundef) #4
declare i64 @getline(i8**, i64*, i32*)
declare i32 @printf(i8*, ...) 
declare i32 @sscanf(i8*,i8*, ...)
declare i32 @puts(i8*)
declare void @exit(i32 noundef)

define void @_printInt(i32 %x) {
       %t0 = getelementptr [4 x i8], [4 x i8]* @dnl, i32 0, i32 0
       call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
       ret void
}

define void @_printString(i8* %s) {
entry:  call i32 @puts(i8* %s)
	ret void
}

define void @_error() {
  entry:
    %msg = getelementptr [15 x i8], [15 x i8]* @err, i32 0, i32 0
    call void @_printString(i8* %msg)
    call void @exit(i32 1)
    ret void
}

define i32 @_readInt() {
entry:	%res = alloca i32
		%input = call i8* @_readString()
    %format = getelementptr [4 x i8], [4 x i8]* @dnl, i32 0, i32 0
		call i32 (i8*,i8*, ...) @sscanf(i8* %input, i8* %format, i32* %res)
		%r = load i32, i32* %res
		ret i32 %r
}

define i8* @_readString() local_unnamed_addr #4 {
  %buff = alloca i8*, align 8 ; ptr to result
  store i8* null, i8** %buff
  %size = alloca i64, align 8 ; size
  store i64 0, i64* %size
  %io = load i32*, i32** @__stdinp
  %length = call i64 @getline(i8** %buff, i64* %size, i32* %io)
  %read = load i8*, i8** %buff
  %pos = sub i64 %length, 1
  %p = getelementptr inbounds i8, i8* %read, i64 %pos
  store i8 0, i8* %p
  ret i8* %read
}

define i8* @addStrings(i8* %fst, i8* %snd) {
	%len_1 = call i64 @strlen(i8* %fst)
	%len_2 = call i64 @strlen(i8* %snd)

	%t.1 = add i64 %len_1, %len_2
	%res_len = add i64 %t.1, 1

	%res_ptr = call i8* @malloc(i64 %res_len)

	call i8* @strcpy(i8* %res_ptr, i8* %fst)
	call i8* @strcat(i8* %res_ptr, i8* %snd)

	ret i8* %res_ptr
}