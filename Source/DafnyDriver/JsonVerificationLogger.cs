using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text.Json.Nodes;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using VC;

namespace Microsoft.Dafny;

public class JsonVerificationLogger : IVerificationResultFormatLogger {
  private TextWriter output;
  private readonly TextWriter fallbackOutput;
  private readonly ProofDependencyManager dependencyManager;

  public JsonVerificationLogger(ProofDependencyManager dependencyManager, TextWriter fallbackOutput) {
    this.dependencyManager = dependencyManager;
    this.fallbackOutput = fallbackOutput;
  }

  public void Initialize(Dictionary<string, string> parameters) {
    output = parameters.TryGetValue("LogFileName", out string filename) ? new StreamWriter(filename) : fallbackOutput;
  }

  private static JsonNode SerializeAssertion(AssertCmd assertion) {
    return new JsonObject {
      ["filename"] = assertion.tok.filename,
      ["line"] = assertion.tok.line,
      ["col"] = assertion.tok.col,
      ["description"] = assertion.Description.SuccessDescription
    };
  }

  public static JsonNode SerializeProofDependency(ProofDependency dependency) {
    return new JsonObject {
      ["startFile"] = dependency.Range.StartToken.Filepath,
      ["startLine"] = dependency.Range.StartToken.line,
      ["startCol"] = dependency.Range.StartToken.col,
      ["endFile"] = dependency.Range.EndToken.Filepath,
      ["endLine"] = dependency.Range.EndToken.line,
      ["endCol"] = dependency.Range.EndToken.col,
      ["description"] = dependency.Description,
      ["originalText"] = dependency.OriginalString()
    };
  }

  public static JsonNode SerializeVcResult(ProofDependencyManager dependencyManager, IReadOnlyList<ProofDependency> potentialDependencies, VerificationRunResult vcResult) {
    var result = new JsonObject {
      ["vcNum"] = vcResult.VcNum,
      ["outcome"] = SerializeOutcome(vcResult.Outcome),
      ["runTime"] = SerializeTimeSpan(vcResult.RunTime),
      ["resourceCount"] = vcResult.ResourceCount,
      ["assertions"] = new JsonArray(vcResult.Asserts.Select(SerializeAssertion).ToArray()),
    };
    if (potentialDependencies is not null) {
      var fullDependencySet = dependencyManager.GetOrderedFullDependencies(vcResult.CoveredElements).ToHashSet();
      var unusedDependencies = potentialDependencies.Where(dep => !fullDependencySet.Contains(dep));
      result["coveredElements"] = new JsonArray(fullDependencySet.Select(SerializeProofDependency).ToArray());
      result["uncoveredElements"] = new JsonArray(unusedDependencies.Select(SerializeProofDependency).ToArray());
    }
    return result;
  }

  private static JsonNode SerializeTimeSpan(TimeSpan timeSpan) {
    return timeSpan.ToString();
  }

  private static JsonNode SerializeOutcome(SolverOutcome outcome) {
    return outcome.ToString();
  }
  private static JsonNode SerializeOutcome(VcOutcome outcome) {
    return outcome.ToString();
  }

  private JsonNode SerializeVerificationResult(VerificationScope scope, IReadOnlyList<VerificationRunResult> results) {
    var trackProofDependencies =
      results.All(o => o.Outcome == SolverOutcome.Valid) &&
      results.Any(vcResult => vcResult.CoveredElements.Any());
    var potentialDependencies =
      trackProofDependencies ? dependencyManager.GetPotentialDependenciesForDefinition(scope.Name).ToList() : null;
    var result = new JsonObject {
      ["name"] = scope.Name,
      ["outcome"] = SerializeOutcome(results.Aggregate(VcOutcome.Correct, (o, r) => MergeOutcomes(o, r.Outcome))),
      ["runTime"] = SerializeTimeSpan(TimeSpan.FromSeconds(results.Sum(r => r.RunTime.Seconds))),
      ["resourceCount"] = results.Sum(r => r.ResourceCount),
      ["vcResults"] = new JsonArray(results.Select(r => SerializeVcResult(dependencyManager, potentialDependencies, r)).ToArray())
    };
    if (potentialDependencies is not null) {
      result["programElements"] = new JsonArray(potentialDependencies.Select(SerializeProofDependency).ToArray());
    }
    return result;
  }

  /// <summary>
  /// This method is copy pasted from a private Boogie method. It will be public Boogie version > 3.0.11
  /// Then this method can be removed
  public static VcOutcome MergeOutcomes(VcOutcome currentVcOutcome, SolverOutcome newOutcome) {
    switch (newOutcome) {
      case SolverOutcome.Valid:
        return currentVcOutcome;
      case SolverOutcome.Invalid:
        return VcOutcome.Errors;
      case SolverOutcome.OutOfMemory:
        if (currentVcOutcome != VcOutcome.Errors && currentVcOutcome != VcOutcome.Inconclusive) {
          return VcOutcome.OutOfMemory;
        }

        return currentVcOutcome;
      case SolverOutcome.TimeOut:
        if (currentVcOutcome != VcOutcome.Errors && currentVcOutcome != VcOutcome.Inconclusive) {
          return VcOutcome.TimedOut;
        }

        return currentVcOutcome;
      case SolverOutcome.OutOfResource:
        if (currentVcOutcome != VcOutcome.Errors && currentVcOutcome != VcOutcome.Inconclusive) {
          return VcOutcome.OutOfResource;
        }

        return currentVcOutcome;
      case SolverOutcome.Undetermined:
        if (currentVcOutcome != VcOutcome.Errors) {
          return VcOutcome.Inconclusive;
        }

        return currentVcOutcome;
      default:
        Contract.Assert(false);
        throw new cce.UnreachableException();
    }
  }

  public void LogScopeResults(VerificationScopeResult scopeResult) {
    verificationResultNode.Add(SerializeVerificationResult(scopeResult.Scope, scopeResult.Results.Select(r => r.Result).ToList()));
  }

  private readonly IList<JsonNode> verificationResultNode = new List<JsonNode>();

  public void Flush() {
    output.Write(new JsonObject {
      ["verificationResults"] = new JsonArray(verificationResultNode.ToArray())
    }.ToJsonString());
    output.Flush();
  }
}