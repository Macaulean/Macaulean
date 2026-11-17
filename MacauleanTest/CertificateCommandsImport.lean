import MacauleanTest.CertificateCommands

example : RationalCertificateTest.I_math.Member RationalCertificateTest.f_math :=
  RationalCertificateTest.f_in_I
example : FiniteCertificateTest.I_math.Member FiniteCertificateTest.f_math :=
  FiniteCertificateTest.f_in_I
example : Macaulean.Algebra.Ideal.Same FiniteCertificateTest.I_math.meaning
    FiniteCertificateTest.same_ideal.basis.output.meaning := FiniteCertificateTest.same_ideal
