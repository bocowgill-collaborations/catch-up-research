import CatchUp.Earlier.CertificateTests

/-! Execute the recovered extraction/checker regressions and corruption controls. -/
def main : IO Unit := CatchUpSearch.CertificateTests.run
