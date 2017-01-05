# deferred.el #

[![Build Status](https://travis-ci.org/kiwanami/emacs-deferred.svg)](https://travis-ci.org/kiwanami/emacs-deferred)
[![Coverage Status](https://coveralls.io/repos/kiwanami/emacs-deferred/badge.svg)](https://coveralls.io/r/kiwanami/emacs-deferred)
[![MELPA](http://melpa.org/packages/deferred-badge.svg)](http://melpa.org/#/deferred)
[![MELPA stable](http://stable.melpa.org/packages/deferred-badge.svg)](http://stable.melpa.org/#/deferred)
[![Tag Version](https://img.shields.io/github/tag/kiwanami/emacs-deferred.svg)](https://github.com/kiwanami/emacs-deferred/tags)
[![License](http://img.shields.io/:license-gpl3-blue.svg)](http://www.gnu.org/licenses/gpl-3.0.html)

deferred.el は非同期処理を抽象化して書きやすくするためのライブラリです。
APIや実装については
[JSDeferred](https://github.com/cho45/jsdeferred "JSDeferred") (by cho45さん)と
[Mochikit.Async](http://mochikit.com/doc/html/MochiKit/Async.html
"Mochikit.Async") (by Bob Ippolitoさん)を参考にしています。

## インストール ##

deferred.elは package.elを使って, [MELPA](http://melpa.org)からインストールすることができます.

## 使い方例 ##

以下のサンプルで例示したソースは deferred-samples.el の中にあります。
eval-last-sexp (C-x C-e) などで実行してみてください。

### 基本 ###

基本的な deferred の連結です。messageにいくつか表示し、ミニバッファから
入力を受け付けます。

Chain:

```el
(deferred:$
  (deferred:next
    (lambda () (message "deferred start")))
  (deferred:nextc it
    (lambda ()
      (message "chain 1")
      1))
  (deferred:nextc it
    (lambda (x)
      (message "chain 2 : %s" x)))
  (deferred:nextc it
    (lambda ()
      (read-minibuffer "Input a number: ")))
  (deferred:nextc it
    (lambda (x)
      (message "Got the number : %i" x)))
  (deferred:error it
    (lambda (err)
      (message "Wrong input : %s" err))))
```


* この式を実行すると、直ちに結果が帰ってきます。
 * 実際の処理自体はすぐ後に非同期で実行されます。
* deferred:$ は deferred を連結するためのマクロです。
 * itには前の式(deferred:nextなど)の返値が入っています。
* 前の deferred 処理の返値が、次の処理の引数になっています。
* 数字以外を入力するとエラーになりますが、 deferred:error でエラーを拾っています。


### タイマーで一定時間後 ###

1秒待ってメッセージを表示します。

Timer:

```el
(deferred:$
  (deferred:wait 1000) ; 1000msec
  (deferred:nextc it
    (lambda (x)
      (message "Timer sample! : %s msec" x))))
```

* deferred:wait の次の処理には、実際に経過した時間が渡ってきます。

### 外部プロセス・コマンド実行 ###

外部プロセスで「ls -la」を実行して結果を現在のバッファに表示します。（素のWindowsで動かす場合は、dirなどに変更してみてください。）

Command process:

```el
(deferred:$
  (deferred:process "ls" "-la")
  (deferred:nextc it
    (lambda (x) (insert x))))
```

* 非同期で実行するため、処理がブロックしたりしません。


### HTTP GET ###

GNUのトップページのHTMLを取ってきて、現在のバッファに貼り付けます（大量のHTMLが張り付きますが、undoで戻せます）。

HTTP GET:

```el
(require 'url)

(deferred:$
  (deferred:url-retrieve "http://www.gnu.org")
  (deferred:nextc it
    (lambda (buf)
      (insert  (with-current-buffer buf (buffer-string)))
      (kill-buffer buf))))
```

### 画像 ###

googleの画像を取ってきてそのままバッファに貼り付けます。

Get an image:

```el
(deferred:$
  (deferred:url-retrieve "http://www.google.co.jp/intl/en_com/images/srpr/logo1w.png")
  (deferred:nextc it
    (lambda (buf)
      (insert-image
       (create-image
        (let ((data (with-current-buffer buf (buffer-string))))
          (substring data (+ (string-match "\n\n" data) 2)))
        'png t))
      (kill-buffer buf))))
```

### 並列 ###

2つの画像を取ってきて、結果がそろったところで各画像のファイルサイズを現在のバッファに表示します。

Parallel deferred:

```el
(deferred:$
  (deferred:parallel
    (lambda ()
      (deferred:url-retrieve "http://www.google.co.jp/intl/en_com/images/srpr/logo1w.png"))
    (lambda ()
      (deferred:url-retrieve "http://www.google.co.jp/images/srpr/nav_logo14.png")))
  (deferred:nextc it
    (lambda (buffers)
      (cl-loop for i in buffers
               do
               (insert
                (format
                 "size: %s\n"
                 (with-current-buffer i (length (buffer-string)))))
               (kill-buffer i)))))
```

* deferred:parallel 内部で、並列に実行できるものは並列に動作します。
* 各処理が完了するかエラーが発生して、すべての処理が完了したところで次の処理が開始されます。
* 次の処理には結果がリストで渡されます。
 * 順番は保持されます
 * alistを渡して名前で結果を選ぶことも出来ます

### deferred組み合わせ、try-catch-finally ###

外部プロセスの wget で画像を取ってきて、ImageMagic の convert コマンドでリサイズし、バッファに画像を表示します。（wget, convertが無いと動きません）
deferred を組み合わせて、非同期処理の try-catch のような構造を作ることが出来ます。

Get an image by wget and resize by ImageMagick:

```el
(deferred:$

  ;; try
  (deferred:$
    (deferred:process "wget" "-O" "a.jpg" "http://www.gnu.org/software/emacs/tour/images/splash.png")
    (deferred:nextc it
      (lambda () (deferred:process "convert" "a.jpg" "-resize" "100x100" "jpg:b.jpg")))
    (deferred:nextc it
      (lambda ()
        (clear-image-cache)
        (insert-image (create-image (expand-file-name "b.jpg") 'jpeg nil)))))

  ;; catch
  (deferred:error it ;
    (lambda (err)
      (insert "Can not get a image! : " err)))

  ;; finally
  (deferred:nextc it
    (lambda ()
      (deferred:parallel
        (lambda () (delete-file "a.jpg"))
        (lambda () (delete-file "b.jpg")))))
  (deferred:nextc it
    (lambda (x) (message ">> %s" x))))
```

* deferred を静的につなげることで、自由に組み合わせることが出来ます。
 * 関数などで個別の deferred 処理を作って、後で一つにまとめるなど。

なお、この例は以下のようにも書けます。（注意：完全に同じ動作ではありません。また、非同期の仕組み上、finallyタスクは必ず実行することを保証するものではありません。）

Try-catch-finally:

```el
(deferred:$
  (deferred:try
    (deferred:$
      (deferred:process "wget" "-O" "a.jpg" "http://www.gnu.org/software/emacs/tour/images/splash.png")
      (deferred:nextc it
        (lambda () (deferred:process "convert" "a.jpg" "-resize" "100x100" "jpg:b.jpg")))
      (deferred:nextc it
        (lambda ()
          (clear-image-cache)
          (insert-image (create-image (expand-file-name "b.jpg") 'jpeg nil)))))
    :catch
    (lambda (err) (insert "Can not get a image! : " err))
    :finally
    (lambda ()
      (delete-file "a.jpg")
      (delete-file "b.jpg")))
  (deferred:nextc it
    (lambda (x) (message ">> %s" x))))
```

### earlierでtimeout ###

外部プロセスで3秒待つコマンドを実行しますが、途中でキャンセルします。

deferred:earlier は parallel と同様に、引数の処理を並列に実行しますが、一番早く完了した処理の結果を次の処理に渡します。他の処理はその時点でキャンセルされます。

Timeout Process:

```el
(deferred:$
  (deferred:earlier
    (deferred:process "sh" "-c" "sleep 3 | echo 'hello!'")
    (deferred:$
      (deferred:wait 1000) ; timeout msec
      (deferred:nextc it (lambda () "canceled!"))))
  (deferred:nextc it
    (lambda (x) (insert x))))
```

* deferred:wait の待つ時間を5秒などにすると、コマンドの結果が渡ってきます。
* エラーは完了と見なされません。すべての処理がエラーになった場合は nil が次に渡ります。
* deferred:parallel と deferred:earlier は lisp の and や or のようなイメージです。

なお、この例は deferred:timeout マクロを使って以下のようにも書けます。

Timeout macro:

```el
(deferred:$
  (deferred:timeout
    1000 "canceled!"
    (deferred:process "sh" "-c" "sleep 3 | echo 'hello!'"))
  (deferred:nextc it
    (lambda (x) (insert x))))
```

### ループとアニメーション・スレッド ###

数秒間カーソールのある位置に文字でアニメーションを表示します。その間、カーソールを自由に動かして普通にEmacsを操作できます。

deferredの処理の中でdeferredオブジェクトを返すと、ソースコードで（静的に）繋がっている次のdeferred処理へ移る前に、返した方のdeferredオブジェクトを実行します（動的なdeferredの接続）。再帰的な構造にしてwaitを入れて負荷を調節することで、マルチスレッドのような処理を実現することが出来ます。

Loop and animation:

```el
(let ((count 0) (anm "-/|\\-")
      (end 50) (pos (point))
      (wait-time 50))
  (deferred:$
    (deferred:next
      (lambda (x) (message "Animation started.")))

    (deferred:nextc it
      (deferred:lambda (x)
        (save-excursion
          (when (< 0 count)
            (goto-char pos) (delete-char 1))
          (insert (char-to-string
                   (aref anm (% count (length anm))))))
        (if (> end (cl-incf count)) ; 止める場合はdeferredでないものを返す（この場合はnil）
            (deferred:nextc (deferred:wait wait-time) self)))) ; 続けるときはdeferredを返す

    (deferred:nextc it
      (lambda (x)
        (save-excursion
          (goto-char pos) (delete-char 1))
        (message "Animation finished.")))))
```

* deferred:lambda は自分自身をselfとして使えるマクロです。再帰的構造を作るのに便利です。

## インタフェース解説 ##

「関数」の章では各関数の簡単な説明を行います。「実行・接続」の章では、deferredオブジェクトの接続（実行順序）などの説明を行います。

### 関数 ###

#### 基本 ####

良く使用する基本的な関数やマクロです。

* deferred:next (callback)
   * 引数：
      * callback: 引数1つか0個の関数
   * 返値：deferredオブジェクト
   * 引数の関数をコールバックとしてラップしたdeferredオブジェクトを生成して返します。また実行キューに入れて非同期実行をスケジュールします。
      * →関数を非同期で実行します。


* deferred:nextc (d callback)
   * 引数：
      * d: deferredオブジェクト
      * callback: 引数1つか0個の関数
   * 返値：deferredオブジェクト
   * 引数の関数をコールバックとしてラップしたdeferredオブジェクトを生成し、引数のdeferredオブジェクトに接続して返します。
      * →前のdeferredの後に関数を実行するように連結します。

* deferred:error (d errorback)
   * 引数：
      * d: deferredオブジェクト
      * errorback: 引数1つか0個の関数
   * 返値：deferredオブジェクト
   * 引数の関数をエラー処理コールバックとしてラップしたdeferredオブジェクトを生成し、引数のdeferredオブジェクトに接続して返します。
      * →前のdeferredでエラーが起きたときに、この関数で処理するようにします。
   * この関数内で例外を発生しなければ、後続のdeferredのコールバック関数が実行されます。

* deferred:cancel (d)
   * 引数：
      * d: deferredオブジェクト
   * 返値：引数のdeferredオブジェクト（無効になっている）
   * 引数のdeferredオブジェクトを無効にして、コールバックやエラーバック関数が実行されないようにします。
   * この関数は引数のdeferredオブジェクトを破壊的に変更します。

* deferred:watch (d callback)
   * 引数：
      * d: deferredオブジェクト
      * callback: 引数1つか0個の関数
   * 返値：deferredオブジェクト
   * 引数の関数をコールバックとエラーバックの両方でラップしたdeferredオブジェクトを生成し、引数のdeferredオブジェクトに接続して返します。
   * 次のdeferredタスクへの値は前のタスクの結果をそのまま渡します。
      * callbackが何を返しても、callback内部でエラーが発生しても、deferredの流れに影響を与えません。
      * callback内部の非同期タスクは後続のdeferredタスクと非同期に実行されます。
   * →deferred処理の流れに割り込んだり、実行状況を監視したいときに使います。

* deferred:wait (msec)
   * 引数：
      * msec: 数値
   * 返値：deferredオブジェクト
   * この関数が実行された時点から引数で指定されたミリ秒待って、後続のdeferredオブジェクトを実行します。
   * 後続のdeferredオブジェクトのコールバック関数の引数には、実際に経過した時間がミリ秒で渡ってきます。

* deferred:$ (forms...)
   * 引数：1つ以上のdeferredフォーム
   * 返値：一番最後のdeferredオブジェクト
   * deferredオブジェクトのチェインを書きやすくするためのアナフォリックマクロです。
   * 一つ前のdeferredオブジェクトが「it」で渡ってきます。

#### ユーティリティ ####

複数のdeferredを扱う関数です。

* deferred:loop (number-or-list callback)
   * 引数：
      * number-or-list: 1以上の整数もしくはリスト
      * callback: 引数1つか0個の関数
   * 返値：deferredオブジェクト
   * 引数の数値で指定された数だけループするようなdeferredオブジェクトを生成して返します。関数には0から始まるカウンタが渡ってきます。
   * 整数ではなくリストが渡ってきた場合は、mapcのようにループします。

* deferred:parallel (list-or-alist)
   * 引数：以下のどちらか
      * 1つ以上のdeferredオブジェクトか引数1つか0個の関数のリスト
      * 1つ以上のシンボルとdeferredオブジェクトか引数1つか0個の関数によるconsセルのリスト（つまりalist）
   * 返値：deferredオブジェクト
   * 引数に与えられたdeferredオブジェクトを並列に実行し、結果を待ち合わせます。
   * 後続のdeferredには結果が順番の保持されたリストとして渡ります。
   * 引数にalistが渡した場合は、結果もalistで渡ります。この場合は順番は保持されません。
   * deferred処理の中でエラーが発生した場合は、結果のリストの中にエラーオブジェクトが入ります。

* deferred:earlier (list-or-alist)
   * 引数：以下のどちらか
      * 1つ以上のdeferredオブジェクトか引数1つか0個の関数のリスト
      * 1つ以上のシンボルとdeferredオブジェクトか引数1つか0個の関数によるconsセルのリスト（つまりalist）
   * 返値：deferredオブジェクト
   * 引数に与えられたdeferredオブジェクトを並列に実行し、最初に帰ってきた結果を後続のdeferredに渡します。
   * 2番目以降の処理はキャンセルされ、結果が帰ってきても無視されます。
   * 引数にalistを渡した場合は、結果はconsセルで渡ります。
   * deferred処理の中でエラーが発生した場合は、結果が帰ってこなかったものとして扱われます。
      * すべての処理がエラーになった場合は、後続のdeferredにnilが渡ります。つまり、エラーバックで処理されません。

#### ラッパー ####

元からある処理をdeferredでラップする関数です。

* deferred:call (function args...)
   * 引数：
      * function: 関数のシンボル
      * args: 引数（可変長）
   * 返値：deferredオブジェクト
   * オリジナルのfuncallを非同期にした関数です

* deferred:apply (function args)
   * 引数：
      * function: 関数のシンボル
      * args: 引数（リスト）
   * 返値：deferredオブジェクト
   * オリジナルのapplyを非同期にした関数です

* deferred:process (command args...) / deferred:process-shell (command args...)
   * 引数：
      * command: 外部実行コマンド
      * args: コマンドの引数(可変長)
   * 返値：deferredオブジェクト
   * 外部コマンドを非同期で実行します。（start-process, start-process-shell-command のラッパー）
   * 外部コマンドのstdoutの結果が文字列として後続のdeferredに渡ります。

* deferred:process-buffer (command args...) / deferred:process-shell-buffer (command args...)
   * 引数：
      * command: 外部実行コマンド
      * args: コマンドの引数(可変長)
   * 返値：deferredオブジェクト
   * 外部コマンドを非同期で実行します。（start-process, start-process-shell-command のラッパー）
   * 外部コマンドのstdoutの結果がバッファとして後続のdeferredに渡ります。
      * バッファの処分は後続のdeferredに任されます。

* deferred:wait-idle (msec)
   * 引数：
      * msec: 数値
   * 返値：deferredオブジェクト
   * 引数で指定されたミリ秒間Emacsがアイドル状態だったときに、後続のdeferredオブジェクトを実行します。
   * 後続のdeferredオブジェクトのコールバック関数の引数には、この関数が呼ばれてから経過した時間がミリ秒で渡ってきます。

* deferred:url-retrieve (url [cbargs])
   * 引数：
      * url: 取ってきたいURL
      * cbargs: コールバック引数（オリジナル関数のもの。省略可。）
   * 返値：deferredオブジェクト
   * urlパッケージにある、オリジナルのurl-retrieveをdeferredでラップした関数です。
   * HTTPで取得した結果が、後続のdeferredにバッファで渡ります。
      * バッファの処分は後続のdeferredに任されます。

* （仮）deferred:url-get (url params)
   * 引数：
      * url: 取ってきたいURL
      * params: パラメーターのalist
   * 返値：deferredオブジェクト
   * パラメーターを指定しやすくした関数です。仮実装ですので今後仕様が変わる可能性があります。

* （仮）deferred:url-post (url params)
   * 引数：
      * url: 取ってきたいURL
      * params: パラメーターのalist
   * 返値：deferredオブジェクト
   * パラメーターを指定しやすくして、POSTでアクセスする関数です。仮実装ですので今後仕様が変わる可能性があります。

#### インスタンスメソッド ####

プリミティブな操作を行う関数です。典型的でないdeferred処理を行いたい場合に、組み合わせて使います。

* deferred:new (callback)
   * 引数：引数1つか0個の関数
   * 返値：deferredオブジェクト
   * 引数の関数をコールバックとしてラップしたdeferredオブジェクトを生成して返します。
   * 実行キューに入れないため、deferred:callbackやdeferred:errorbackが呼ばれない限り実行されません。
   * 一時停止して他のイベントを待つような、deferredチェインを作りたいときに使います。 → deferred:wait のソースなどを参考。

* deferred:succeed ([value])
   * 引数：値（省略可）
   * 返値：deferredオブジェクト
   * 引数の値を使って、既にコールバックが呼ばれた状態のdeferredを返します。
   * 後続のdeferredは接続されたら直ちに（同期的に）実行されます。

* deferred:fail ([error])
   * 引数：値（省略可）
   * 返値：deferredオブジェクト
   * 引数の値を使って、既にエラーバックが呼ばれた状態のdeferredを返します。
   * 後続のdeferredは接続されたら直ちに（同期的に）実行されます。

* deferred:callback (d [value])
   * 引数：
      * d: deferredオブジェクト
      * value: 値（省略可）
   * 返値：deferredオブジェクトか、結果値
   * 引数のdeferredオブジェクトを同期的に開始します。
   * ただし、同期的な実行は初回のみで、引数のdeferred以降のdeferredオブジェクトは非同期に実行されます。

* deferred:callback-post (d [value])
   * 引数：
      * d: deferredオブジェクト
      * value: 値（省略可）
   * 返値：deferredオブジェクトか、結果値
   * 引数のdeferredオブジェクトを非同期に開始します。

* deferred:errorback (d [error])
   * 引数：
      * d: deferredオブジェクト
      * error: 値（省略可）
   * 返値：deferredオブジェクトか、結果値
   * 引数のdeferredオブジェクトからエラーバックを同期的に開始します。

* deferred:errorback-post (d [error])
   * 引数：
      * d: deferredオブジェクト
      * error: 値（省略可）
   * 返値：deferredオブジェクトか、結果値
   * 引数のdeferredオブジェクトからエラーバックを非同期に開始します。


### ユーティリティマクロ ###

いくつかの便利なマクロを用意しています。マクロですので、スコープや評価順序などに注意して予想外の動作に気をつけてください。

* deferred:try (d &key catch finally)
   * 引数：
      * d: deferredオブジェクト
      * catch: [キーワード引数] dのタスクを実行中にエラーが起きたときに実行される関数。（マクロ展開によって deferred:error の引数に入る）
      * finally: [キーワード引数] dのタスクが正常・エラーに関わらず終了したあとに実行する関数（マクロ展開によって deferred:watch の引数に入る）
   * 返値：deferredオブジェクト
   * 非同期処理で try-catch-finally のような処理を実現するマクロです。所詮非同期なので、メインのdeferredタスクの内容によっては、finallyタスクに処理が回ってこない可能性もあります。
   * deferred:error と deferred:watch を使って実装しています。

* deferred:timeout (msec timeout-form d)
   * 引数：
      * msec: 数値
      * timeout-form: キャンセル時に評価する sexp-form
      * d: deferredオブジェクト
   * 返値：deferredオブジェクト
   * dのタスクを開始してmsecミリ秒経過した場合、dのタスクをキャンセルして、timeout-formの結果を後続のdeferredに渡します。
   * deferred:earlierとdeferred:waitを使って実装しています。

* deferred:process〜
   * deferred:processc (d command args...)
   * deferred:process-bufferc (d command args...)
   * deferred:process-shellc (d command args...)
   * deferred:process-shell-bufferc (d command args...)
   * 引数：
      * d: deferredオブジェクト
      * command: 外部実行コマンド
      * args: コマンドの引数(可変長)
   * 返値：deferredオブジェクト
   * 外部コマンドを非同期で実行するdeferredオブジェクトをdに接続します。
   * deferred:nextc の lambda の中に元の関数を埋め込んで実装しています。

### 実行・接続 ###

#### 処理開始について ####

関数の中には処理を自動的に開始するものとしないものがあります。

以下の関数は、非同期実行用のキューにdeferredオブジェクトを登録します。つまり、自動的に実行を開始します。

* next
* wait
* loop
* parallel
* earlier
* call, apply
* process
* url-retrieve, url-get, url-post

new は callback や errorback を呼ぶまで実行が開始されません。他のイベントを待って実行を開始するような用途で使います。

deferredオブジェクトは先にコールバックを実行しておいて、後で後続のdeferredオブジェクトをつなげることも出来ます。つまり、一番最後のdeferredオブジェクトは、続きのdeferredオブジェクトが接続されるまで結果を保持し続けます。succeed と fail は、そのような既に実行された状態の deferred を生成します。

#### ソースコード上のでの接続 ####

deferredオブジェクトを$などを使ってソースコード上で連結することを、静的な接続と呼びます。

これはdeferredの基本的な使い方で、コールバック処理の書き方を変えたものだと言えます。

処理がコード上に並びますので読みやすく、流れも理解しやすいです。通常、このパターンを使います。

#### 実行時に接続 ####

deferred処理の中でdeferredオブジェクトを返すと、静的に接続された（ソースコード上の）後続のdeferredオブジェクトの前に、そのdeferredを割り込ませます。

この動作により、ループや分岐などの高度な非同期処理を行うことができます。

## ポイント ##

ここでは、いくつかの実装上のポイントを示します。

### レキシカルスコープ ###

deferredの処理に値を持って行く場合、let などを用いてレキシカルスコープを使うと大変便利です。

特に、一連のdeferred処理の中で共通に使う値にレキシカルスコープを使うと、ローカル変数のようにアクセスすること出来るため、非同期処理のために値をグローバルに保持しておく必要が無くなります。

let 例:

```el
(let ((a (point)))
  (deferred:$
    (deferred:wait 1000)
    (deferred:nextc it
      (lambda (x)
        (goto-char a)
        (insert "here!")))))
```

逆に、letでレキシカルスコープにバインドしていないシンボルを参照しようとして、エラーになることがよくあります。

### カレント状態 ###

save-execursion や with-current-buffer など、S式の範囲で状態を保持する関数がありますが、deferred関数を囲っていても非同期で処理される時点では無効になっています。

ダメな例:

```el
(with-current-buffer (get-buffer "*Message*")
  (deferred:$
    (deferred:wait 1000)
    (deferred:nextc it
      (lambda (x)
        (insert "Time: %s " x) ; ここは *Message* バッファとは限らない！
      ))))
```

このような場合は、レキシカルスコープなどでdeferredの中にバッファオブジェクトを持って行き、その中でバッファを切り替える必要があります。

改善例:

```el
(let ((buf (get-buffer "*Message*")))
  (deferred:$
    (deferred:wait 1000)
    (deferred:nextc it
      (lambda (x)
        (with-current-buffer buf ; 非同期処理の中で設定する
          (insert "Time: %s " x))))))
```

### lambdaの返り値に気を使う ###

先に述べたとおり、deferredの処理の中でdeferredオブジェクトを返すと、動的な接続によりdeferred処理が割り込まれます。しかしながら、意図せずdeferredオブジェクトを返してしまい、実行順序がおかしくなり、バグに繋がるケースがあります。

そのため、deferredのコールバックで返す値には気をつける必要があります。特に値を返さない場合は、予防として明示的にnilを返すようにするといいと思います。

### デバッグ ###

通常の処理に比べて、非同期の処理はデバッグが難しいことが多いです。デバッガが使える場面も多いですが、デバッガで停止中に他の非同期処理が行われたりすることがあるため、正しくデバッグできないこともあります。その場合は、message文をちりばめるとか、独自のログバッファに出力するなどしてデバッグすることが確実だと思います。

意図せず無限ループに陥って、非同期処理が延々と走り続けてしまうことがあります。その場合は、 deferred:clear-queue 関数を呼ぶ（M-xからも呼べます）ことで、実行キューを空にして止めることが出来ます。

非同期のタスクで発生したエラーは、エラーバックで拾わないと最終的にはmessageに表示されます。deferredの実装内部は condition-case で囲っていますので、デバッガでエラーを拾いたい場合は toggle-debug-on-error でデバッガを有効にすると同時に、 deferred:debug-on-signal を t に設定して発生したエラー取得するようにしてください。

deferred:sync! 関数を使うことによって、deferred タスクを待ち合わせて同期的にすることができます。ただし、待ち合わせは完全ではないため、テストやデバッグ目的にのみ使うようにして、実アプリでは使わないようにしてください。

### マクロ ###

deferred.elを使うと、nextcやlambdaをたくさん書くことになると思います。これらをマクロでラップすることで短く書くことが可能になります。deferred.elのテストコードのtest-deferred.elでは、マクロを使ってとにかく短く書いています。

一方、マクロでlambdaを隠蔽することで、フォームを実行した値を渡したいのか、あるいは非同期に実行される関数が引数なのか、分かりづらくなるおそれがあります。そういった理由からdeferred.elでは積極的に便利なマクロを提供していません。マクロで短く書く場合には、実行されるタイミングに気をつける必要があります。

### deferred入門 ###

deferredによってどのようなことが可能になるかなどについては、JavaScriptの例ではありますが、以下のドキュメントが大変参考になると思います。

* [JSDeferred紹介](http://cho45.stfuawsc.com/jsdeferred/doc/intro.html "JSDeferred紹介")
* [特集：JSDeferredで，面倒な非同期処理とサヨナラ｜gihyo.jp … 技術評論社](http://gihyo.jp/dev/feature/01/jsdeferred "特集：JSDeferredで，面倒な非同期処理とサヨナラ｜gihyo.jp … 技術評論社")


* * * * *

(C) 2010-2016  SAKURAI Masashi  All rights reserved.
m.sakurai at kiwanami.net
