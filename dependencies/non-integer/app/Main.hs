{-# LANGUAGE EmptyDataDecls        #-}

module Main where
import Criterion.Main
import System.IO (isEOF)

import NonIntegral

import qualified Data.Fixed as FP

data E34

instance FP.HasResolution E34 where
    resolution _ = 10000000000000000000000000000000000

type Digits34 = FP.Fixed E34

type FixedPoint = Digits34

precision :: FixedPoint
precision = 10000000000000000000000000000000000

epsilon :: FixedPoint
epsilon = 100000000000000000

doTestsFromStdin = do
  b <- isEOF
  if b then return ()
    else do
    line <- getLine
    let base     = read (takeWhile (/= ' ') line)        :: FixedPoint
    let exponent = read (tail $ dropWhile (/= ' ') line) :: FixedPoint
    putStrLn $ show ((base / precision) *** (exponent / precision))
            ++ " " ++ show (exp' (base / precision))
    main

benchmarkData :: [(FixedPoint, FixedPoint)]
benchmarkData = [
 (13.2537787738760641755376502809034752, 45.9650132023219801122678173987766272),
 (21.9959186212478939576566810908033024, 67.9864716740685320723722320893444096),
 (93.5692896226738780239819442090934272, 52.0416372022747454755038068918452224),
 (3.5572110464847438658621000753610752, 53.0700193141057148796603927067885568),
 (0.8698186061599178016839257995345920, 6.7842237262567550912485920681754624),
 (68.7772712409045218677237524992098304, 93.1436494969692729683863493865897984),
 (52.7928777759906053349458218592501760, 65.4918962180522563964940116488617984),
 (70.2190594499176628519353723293532160, 76.3198039998634025568863980865191936),
 (4.8464513386311943174129704947941376, 32.9234226160007695845405254423150592),
 (75.7410486132585916475077118859935744, 36.6338670891576770364321402200260608),
 (98.3550286321034279316900414304026624, 75.4355835205582835881179333959614464),
 (7.3685882820231065878204334016036864, 88.5707128815841388784728276161527808),
 (43.7411405515639515926670748791341056, 47.8731765118408124102889574557024256),
 (27.5906840076478324717730408223997952, 16.7507200194652839689498413431259136),
 (89.8656286732214356920544015218114560, 6.1564327533513653582490711808278528),
 (50.5522894934610842134489594628931584, 32.0032941085453044152882062648410112),
 (49.4976685206683080322997356437962752, 9.1732894580629795064426413072318464),
 (7.4749075222416952086275606162964480, 38.5142147968053562835285961001140224),
 (91.4817442071026505531811954721554432, 46.5445824948437078206920528205185024),
 (5.1083983708707576175800161188970496, 77.1204547001944331932077135063154688),
 (12.6365375577727370437324925436952576, 68.9455301054184269138551670428401664),
 (63.0543418124007866926297675984797696, 72.6411998660791682802467003426668544),
 (88.9572214067262526845885219646472192, 30.7321830882615579596165570289991680),
 (51.4273702178878126522261227247239168, 84.6981560313644065403306525232988160),
 (84.2510639570235198523653107629424640, 41.6394615428571792155199886898233344),
 (46.8917368501955056412849664233046016, 17.9327703682644204038452725428518912),
 (57.2654810708495527940453948329033728, 3.4053754301980716094514512284090368),
 (49.9480119058587559718046117430034432, 74.9292651237894527529873173079130112),
 (89.1737481571761229349640790133964800, 84.3039612731397230566496953287311360),
 (21.3751514550890100882157511395770368, 13.1427261803096352444070168075698176),
 (27.5588147476393039766306025516302336, 41.5293263029114314840112339361988608),
 (71.0819592743420713183829908932001792, 24.0910804861094316309518050922594304),
 (31.8539536308485575248923454156570624, 65.3058686218740237105630705788911616),
 (68.2346213683964440285440047142928384, 38.8725337017916733399386692947804160),
 (14.8533003145273304595931834733297664, 84.6575659665436275762825507196895232),
 (95.6408826703636961457331157929558016, 14.9151562014803854592052189749837824),
 (40.9766693808528814907580727271882752, 56.5898680556387154508400043388567552),
 (48.9514549205617746954221331043844096, 96.2095140961101693057998967919345664),
 (20.0757199047852903308286891936186368, 63.0269156408397464403517396458930176),
 (65.2253741434411806763695019034411008, 80.4072996077956386107013783921623040),
 (47.7431802939952072643957799438516224, 20.4250334503042885392104947359678464),
 (90.2673498950769205614891313024466944, 14.3021031915461385783612022477291520),
 (41.1313035719149267110384665379209216, 88.6648371140698548984003698213519360),
 (16.3198551658806785295810092033114112, 36.6339028556710894770033709453148160),
 (13.6109368024056806920294756203364352, 45.6307284227464165454251751647477760),
 (45.3300169157853520641659177483108352, 93.2674400657552088906454347764727808),
 (21.6248384085550393713395542226108416, 90.9921885535789620214810090856775680),
 (86.1859835972937220921010113512210432, 50.6955875144886865962696847428419584),
 (81.8561483120320598691226029106659328, 46.3244979422694781742782240662749184),
 (63.3738700237518516087758565148721152, 82.5697386980394222520198913320812544)
  ]

benchmarks = zip (map show ([0..] :: [Int])) benchmarkData

main :: IO ()
main = defaultMain [
  bgroup "exp" [bench "1" $
                whnf
                 ((***) (13.2537787738760641755376502809034752::FixedPoint))
                 (45.9650132023219801122678173987766272) ] --(map \(idx, (x, y)) -> bench idx $ x *** y )
  ]
