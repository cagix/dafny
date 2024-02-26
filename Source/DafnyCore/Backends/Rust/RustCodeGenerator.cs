using System;
using System.IO;
using System.Linq;
using Dafny;

namespace Microsoft.Dafny.Compilers {

  class RustCodeGenerator : DafnyWrittenCodeGenerator {

    public DafnyOptions Options { get; set; }

    public RustCompiler(DafnyOptions options) {
      this.Options = options;
    }

    public override ISequence<Rune> Compile(Sequence<DAST.Module> program) {
      if (Options.Get(CommonOptionBag.UnicodeCharacters)) {
        return DCOMP.COMP.Compile(program);
      } else {
        return DCOMPUTF16.COMP.Compile(program);
      }
      
    }

    public override ISequence<Rune> EmitCallToMain(string fullName) {
      var splitByDot = fullName.Split('.');
      var convertedToUnicode = Sequence<Sequence<Rune>>.FromArray(splitByDot.Select(s => (Sequence<Rune>)Sequence<Rune>.UnicodeFromString(s)).ToArray());
      if (Options.Get(CommonOptionBag.UnicodeCharacters)) {
        return DCOMP.COMP.EmitCallToMain(convertedToUnicode);
      } else {
        return DCOMPUTF16.COMP.EmitCallToMain(convertedToUnicode);
      }
    }

  }

}