package viper.carbon

import viper.silver.reporter.StdIOReporter
import viper.silver.testing.BackendTypeTest
import viper.silver.verifier.Verifier
import org.scalatest.DoNotDiscover

@DoNotDiscover
class CarbonBackendTypeTest extends BackendTypeTest {
  override val verifier: Verifier = CarbonVerifier(StdIOReporter())
}
