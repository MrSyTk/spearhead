# Spearhead
Spearheadは，「型付きDSLに対する型安全なプログラム変換フレームワーク」として発表した最適化記述フレームワークです．

# Requirement

* ocaml 4.04.0+BER
* omake 0.10.3
* base-metaocaml-ocamlfind

# Usage
初期状態として，[1]に記載のDeforesataionの実装が記述されており，文字列検索のコードを対象に動作します．
この状態では，第4引数kのみが重要です．A<sup>k</sup>Bをneedleとする文字列検索コードを出力します．

```bash
omake
./search1.run 1 1 1 2
ls search2_naive.ml search2_kmp.ml
```
とすると，AABについて検索するコードのDeforestationの結果と適用前のOCamlコードが得られます．得られたファイルは，
```bash
ocamlopt search2_kmp.ml -o kmp2
./kmp2 2000
```
とコンパイルして実行すると，A<sup>2000</sup>Bについての実行時間を出力します．

# Note
プログラム変換後の後処理として，不使用変数の除去や相互再帰への変換を行っています．特に，後者はスーパーコンパイラ・Deforestationでしか正しい変換ではないのでご注意下さい．この後処理を適用したくない場合は，UnTypeモジュールの代わりにCモジュールを使って下さい．

# Author

* 高木尚
* takaki.sho.ry@alumni.tsukuba.ac.jp

# License
Spearhead is under [MIT license](https://en.wikipedia.org/wiki/MIT_License).

# 参考文献
[1]Morten Heine Sørensen, Robert Glück, and Neil D. Jones. A positive supercompiler. *J. Funct. Program.* , Vol. 6, No. 6, pp. 811–838, 1996.
