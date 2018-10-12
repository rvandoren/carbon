package viper.carbon.modules

import viper.carbon.boogie.{Exp, LocalVar, RealLit}
import viper.silver.ast.LocationAccess
import viper.silver.verifier.{PartialVerificationError, VerificationError, reasons}
import viper.silver.{ast => sil}

/**
 * Created by Gaurav on 02.05.2015.
 */
sealed trait TransferableEntity {
  def rcv: Exp
  def loc: Exp
  def transferAmount: Exp
  def originalSILExp: sil.Exp

  def transferError(error: PartialVerificationError):VerificationError
}

object TransferableEntity {
  def unapply(te: TransferableEntity) = Some((te.rcv,te.loc,te.transferAmount))
}

sealed trait TransferableAccessPred extends TransferableEntity {
  override def transferError(error: PartialVerificationError):VerificationError =
    originalSILExp.loc match {
      case loc: LocationAccess => error.dueTo(reasons.InsufficientPermission(loc))
      case other => sys.error(s"Unexpectedly found resource access node $other")
  }
  override def originalSILExp: sil.AccessPredicate
}

object TransferableAccessPred {
  def unapply(tap: TransferableAccessPred) = Some((tap.rcv,tap.loc,tap.transferAmount, tap.originalSILExp))
}

case class TransferableFieldAccessPred(rcv: Exp, loc:Exp, transferAmount: Exp,originalSILExp: sil.AccessPredicate) extends TransferableAccessPred

case class TransferablePredAccessPred(rcv: Exp, loc:Exp, transferAmount: Exp,originalSILExp: sil.AccessPredicate) extends TransferableAccessPred

case class TransferableWand(rcv:Exp, loc: Exp, transferAmount: Exp,originalSILExp: sil.MagicWand) extends TransferableEntity {
  override def transferError(error: PartialVerificationError): VerificationError = {
    error.dueTo(reasons.MagicWandChunkNotFound(originalSILExp))
  }
}
