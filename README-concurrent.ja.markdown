# concurrent.el #

concurrent.elは、良くある非同期処理を抽象化したライブラリです。スレッド、セマフォ、イベント管理などがあります。他の環境のライブラリや並行プログラミングのアイデアを参考にしました。

## インストール ##

deferred.el と concurrent.elをload-pathに置いてください。

[auto-install.el](http://d.hatena.ne.jp/rubikitch/20091221/autoinstall "auto-install.el]") を使うことで、以下の式を実行することでインストールできます。

インストール実行:

    (auto-install-from-url https://github.com/kiwanami/emacs-deferred/raw/master/deferred.el")
    (auto-install-from-url https://github.com/kiwanami/emacs-deferred/raw/master/concurrent.el")


## 使い方例 ##

以下のサンプルで例示したソースは concurrent-samples.el の中にあります。
eval-last-sexp (C-x C-e) などで実行してみてください。

### Threadの例

lexical-letを評価するとその場でアニメーションします。引数の時間は、bodyの処理の間隔です。

Thread:

    (lexical-let 
        ((count 0) (anm "-/|\\-")
         (end 50) (pos (point)))
      (cc:thread 
       60 
       (message "Animation started.")
       (while (> end (incf count))
         (save-excursion
           (when (< 1 count)
             (goto-char pos) (delete-char 1))
           (insert (char-to-string 
                    (aref anm (% count (length anm)))))))
       (save-excursion
         (goto-char pos) (delete-char 1))
       (message "Animation finished.")))
    
whileを使うことでスレッドをループさせることが出来ます。whileの中身は一気に実行されます。

無限ループや重い処理でEmacsが固まらないように注意してください。もし無限ループに突入してしまったり、固まってしまったら deferred:clear-queue コマンドで回復できる可能性があります。


### Generatorの例

fib-genにジェネレーターを作ります。ジェネレーター生成body内のyield関数で値を返します。値はコールバックで値を受け取ります。

Generator:

    (setq fib-list nil)
    (setq fib-gen
          (lexical-let ((a1 0) (a2 1))
            (cc:generator
             (lambda (x) (push x fib-list)) ; コールバックで結果受け取り
             (yield a1)
             (yield a2)
             (while t
               (let ((next (+ a1 a2)))
                 (setq a1 a2
                       a2 next)
                 (yield next))))))
    
    (funcall fib-gen) ; 何度か呼んでみる
    (funcall fib-gen) (funcall fib-gen)
    (funcall fib-gen) (funcall fib-gen)
    
    fib-list ; => (3 2 1 1 0)
    
### Semaphoreの例

cc:semaphore-acquire 関数が deferred を返すので、それに続けて実行させたいタスクをつなげていきます。時系列で挙動が変わっていくのでコード中に簡単な説明を書いてみました。

Semaphore:

    ;; permit=1のセマフォ作成
    (setq smp (cc:semaphore-create 1))
    
    ;; 続けて3つ実行しようとする
    (deferred:nextc (cc:semaphore-acquire smp)
      (lambda(x) 
        (message "go1")))
    (deferred:nextc (cc:semaphore-acquire smp)
      (lambda(x) 
        (message "go2")))
    (deferred:nextc (cc:semaphore-acquire smp)
      (lambda(x) 
        (message "go3")))
    
    ;; => 1つ目だけ実行されて go1 が表示される
    
    (cc:semaphore-release smp) ; permitを返す
    
    ;; => 2つ目が実行されて go2 が表示される
    
    (cc:semaphore-waiting-deferreds smp) ; go3 を表示するdeferred
    
    (cc:semaphore-release-all smp) ; => permitを初期化して go3 を表示するdeferredを返す
    
    (cc:semaphore-waiting-deferreds smp) ; => nil

### Dataflowの例：

cc:dataflow-environment 関数で変数を格納する「環境」を作ります。 cc:dataflow-get は値の取得とそれに続くタスクをつなげる deferred を返します。 cc:dataflow-set で値をバインドします。例ではキーに文字列を使っていますが、キーには任意のオブジェクトを指定できます。

Dataflow:

    (setq dfenv (cc:dataflow-environment))
    
    ;; ○基本の使い方
    
    ;; ↓同期的に値を取得。ブロックしない。
    (cc:dataflow-get-sync dfenv "abc") ; => nil まだ値が無い。
    
    (deferred:$ ; abc という値を取ってきて表示する処理
      (cc:dataflow-get dfenv "abc")
      (deferred:nextc it
        (lambda (x) (message "Got abc : %s" x))))
    ;; => 値がないので処理はブロックしたまま
    
    (cc:dataflow-set dfenv "abc" 256) ; 値をセット
    ;; => ここで先ほどブロックしていた処理が再開し、 "Got abc : 256" が表示される
    
    (cc:dataflow-get-sync dfenv "abc") ; => 256
    
    (cc:dataflow-clear dfenv "abc") ; 値を未バインドに戻す
    
    (cc:dataflow-get-sync dfenv "abc") ; => nil
    
    ;; ○リストをキーにする
    
    (deferred:$
      (cc:dataflow-get dfenv '("http://example.com/a.jpg" 300))
      (deferred:nextc it
        (lambda (x) (message "a.jpg:300 OK %s" x))))
    
    (cc:dataflow-set dfenv '("http://example.com/a.jpg" 300) 'jpeg)
    
    ;; => a.jpg:300 OK jpeg
    
    ;; ○2つの値を待ち受ける
    
    (deferred:$ ; abc, def の2つの値を使う
      (deferred:parallel
        (cc:dataflow-get dfenv "abc")
        (cc:dataflow-get dfenv "def"))
      (deferred:nextc it
        (lambda (values) 
          (apply 'message "Got values : %s, %s" values)
          (apply '+ values)))
      (deferred:nextc it
        (lambda (x) (insert (format ">> %s" x)))))
    ;; => もちろんブロックする
    
    (cc:dataflow-get-waiting-keys dfenv) ; => ("def" "abc")
    (cc:dataflow-get-avalable-pairs dfenv) ; => ((("http://example.com/a.jpg" 300) . jpeg))
    
    (cc:dataflow-set dfenv "abc" 128) ; ここではまだブロックしたまま
    (cc:dataflow-set dfenv "def" 256) ; ここでやっと動く
    ;; => Got values : 128, 256

### Signalの例：

cc:signal-channel でシグナルを流すチャンネルを作成します。その後、signalに応答する処理を接続していきます。

    ;; シグナルのチャンネルを作成
    (setq channel (cc:signal-channel))
    
    (cc:signal-connect ; foo というシグナルを拾う
     channel 'foo
     (lambda (event) (message "Signal : %S" event)))
    
    (cc:signal-connect
     channel t  ; t にするとすべてのシグナルを拾う
     (lambda (event) 
       (destructuring-bind (event-name (args)) event
         (message "Listener : %S / %S" event-name args))))
    
    (deferred:$ ; deferred で非同期タスクを接続できる
      (cc:signal-connect channel 'foo)
      (deferred:nextc it
        (lambda (x) (message "Deferred Signal : %S" x))))
    
    (cc:signal-send channel 'foo "hello signal!")
    ;; =>
    ;; Listener : foo / "hello signal!"
    ;; Signal : (foo ("hello signal!"))
    ;; Deferred Signal : (foo ("hello signal!"))
    
    (cc:signal-send channel 'some "some signal!")
    ;; =>
    ;; Listener : some / "some signal!"

    
dataflowの内部には、変数へのアクセスやバインドのシグナルを発信するchannelがあります。これを使って、未バインドの変数に値を作成してセットするようなことが出来ます。

signalやdataflowは、カスケード接続して親子関係を構築できます。例えば、親dataflowにデフォルト値（フォールバックの値）を入れておくとか、channelで親子関係を構築してローカルなイベントとグローバルなイベントを分けて効率的にイベントを管理するなどが出来ます。

## インタフェース解説 ##

### Thread

* cc:thread (wait-time-msec &rest body)
   * 引数：
      * wait-time-msec: タスク間の間隔（ミリ秒）
   * 返値：Threadオブジェクト（今のところ使い道無し）
   * スレッドを作成して開始します
   * bodyのS式が一つずつ非同期で実行されます。その間隔が wait-time-msec で指定された時間です。
   * bodyの中に while があった場合は、特別にループとして処理します。
   * 無限ループや重い処理でEmacsが固まらないように注意してください。もし無限ループに突入してしまったり、固まってしまったら deferred:clear-queue コマンドで回復できる可能性があります。
 
### Generator

* cc:generator (callback &rest body)
   * 引数：
      * callback: yieldした値を受け取る関数
      * body: Generatorの中身
   * 返値：Generatorを実行する関数
   * Threadと同様に、bodyのS式が一つずつ非同期で実行されます。
   * bodyの中に while があった場合は、特別にループとして処理します。
   * bodyの内で yield 関数を使う（実際にはマクロで置換されます）と、callbackで指定した関数に値が渡って処理が停止します。
   * 再度 Generator 関数を実行すると停止した位置から開始します。

### Semaphore

* cc:semaphore-create (permits-num)
   * 引数：
      * permits-num: 許可数
   * 返値：Semaphoreオブジェクト
   * セマフォオブジェクトを作成します。

* cc:semaphore-acquire (semaphore)
   * 引数：
      * semaphore: Semaphoreオブジェクト
   * 返値：Deferredオブジェクト
   * 返したDeferredオブジェクトに、実行数を制限したいタスクをつなげます。
   * 実行する際、許可数を1つ消費します。許可数が0になったら、以降のタスクは待たされます。
   * 実行可能なら、返したDeferredタスクがすぐに実行されます。
   * 実行可能でなければ、許可数が戻るまで返したDeferredタスクは待たされます。

* cc:semaphore-release (semaphore)
   * 引数：
      * semaphore: Semaphoreオブジェクト
   * 返値：Semaphoreオブジェクト
   * 許可数を一つ戻します。その際、待っているタスクがあれば実行されます。
   * 許可数は自動では戻りませんので、 cc:semaphore-release を呼ぶのはプログラマの責任です。

* cc:semaphore-with (semaphore body-func &optional error-func)
   * 引数：
      * semaphore: Semaphoreオブジェクト
      * body-func: 実行数を制御したいタスクの関数
      * error-func: 発生したエラーを処理する関数（deferred:errorで接続される）
   * 返値：Deferredオブジェクト
   * acquireとreleaseを前後で行う関数です。特に理由がない限りは、acquireとreleaseを自分で書くよりも、こちらを使う方が安全で楽です。


* cc:semaphore-release-all (semaphore)
   * 引数：
      * semaphore: Semaphoreオブジェクト
   * 返値：実行待ちだったDeferredオブジェクト
   * 許可数を強制的に初期値に戻します。デバッグ時や状態をリセットしたいときに使います。

* cc:semaphore-interrupt-all (semaphore)
   * 引数：
      * semaphore: Semaphoreオブジェクト
   * 返値：Deferredオブジェクト
   * 実行待ちのタスクがなければ、すぐに実行するDeferredオブジェクトを返します。
   * 現在実行待ちのタスクがあれば取り除いて、現在実行中のタスクの次に実行されるDeferredオブジェクトを返します。
   * 割り込みしたいときに使います。

### Signal

* cc:signal-channel (&optional name parent-channel)
   * 引数：
      * name: このチャンネルの名前。主にデバッグ用。
      * parent-channel: 上流のチャンネルオブジェクト。
   * 返値：チャンネルオブジェクト
   * 新しいチャンネルを作成します。
   * 上流のシグナルは下流に流れてきますが、下流から上流には cc:signal-send-global を使わない限り流れません。

* cc:signal-connect (channel event-sym &optional callback)
   * 引数：
      * channel: チャンネルオブジェクト
      * event-sym: イベント識別シンボル
      * callback: 受け取り関数
   * 返値：Deferredオブジェクト
   * シグナルを受信するタスクを追加します。
   * event-sym が t の場合は、すべてのシグナルを受信します。
   * 通常はこの関数の返値にシグナルを受信する非同期タスクを接続します。

* cc:signal-send (channel event-sym &rest args)
   * 引数：
      * channel: チャンネルオブジェクト
      * event-sym: イベント識別シンボル
      * args: イベント引数
   * 返値：なし
   * シグナルを発信します。
   * args は、受信側で (lambda (event) (destructuring-bind (event-sym (args)) event ... )) のようにすると受け取れます。


* cc:signal-send-global (channel event-sym &rest args)
   * 引数：
      * channel: チャンネルオブジェクト
      * event-sym: イベント識別シンボル
      * args: イベント引数
   * 返値：なし
   * 上流のチャンネルにシグナルを送信します。

* cc:signal-disconnect (channel deferred)
   * 引数：
      * channel: チャンネルオブジェクト
      * deferred: チャンネルから取り除きたいDeferredオブジェクト
   * 返値：削除されたDeferredオブジェクト
   * チャンネルから受信タスクを取り除きます。

* cc:signal-disconnect-all (channel)
   * 引数：
      * channel: チャンネルオブジェクト
   * 返値：なし
   * すべての受信タスクを取り除きます。

### Dataflow

* cc:dataflow-environment (&optional parent-env test-func channel)
   * 引数：
      * parent-env: デフォルト値として使うDataflowオブジェクト
      * test-func: keyの比較関数
      * channel: チャンネルオブジェクト
   * 返値：Dataflowオブジェクト
   * 新しくDataflowオブジェクトを作成して返します。
   * channelは引数で与えなかった場合は、内部新しいチャンネルオブジェクトを作成します。
   * 以下のシグナルがチャンネルに送信されます
      * get-first : 初回未バインド変数を参照したとき
      * get-waiting : 2回目以降の未バインド変数を参照したとき
      * set : 値をバインドしたとき
      * get : バインドされた値を参照したとき
      * clear : バインド解除されたとき
      * clear-all : すべてのバインドが解除されたとき

* cc:dataflow-get (df key)
   * 引数：
      * df: Dataflowオブジェクト
      * key: 変数キー
   * 返値：変数の値を受け取るDeferredオブジェクト
   * 変数の値を受け取るDeferredタスクを返すので、変数の値を使う処理を接続します。
   * 変数の値がバインドされていれば、直ちに実行されます。
   * 変数の値がバインドされていなければ、返されたDeferredタスクはバインドされるまで実行されません。

* cc:dataflow-get-sync (df key)
   * 引数：
      * df: Dataflowオブジェクト
      * key: 変数キー
   * 返値：nil か値
   * 変数の値を同期的に参照します。
   * 値がバインドされていなければ nil を返します。

* cc:dataflow-set (df key value)
   * 引数：
      * df: Dataflowオブジェクト
      * key: 変数キー
      * value: 値
   * 返値：なし
   * 変数に値をバインドします。
   * もし、すでにバインドされている変数にバインドしようとした場合はエラーが発生します。

* cc:dataflow-clear (df key)
   * 引数：
      * df: Dataflowオブジェクト
      * key: 変数キー
   * 返値：なし
   * 変数を未バインドに戻します。

* cc:dataflow-get-avalable-pairs (df)
   * 引数：
      * df: Dataflowオブジェクト
   * 返値：バインドされている変数キーと値の alist

* cc:dataflow-get-waiting-keys (df)
   * 引数：
      * df: Dataflowオブジェクト
   * 返値：未バインドで、受け取り待ちのタスクが存在する変数キーのリスト

* cc:dataflow-clear-all (df)
   * 引数：
      * df: Dataflowオブジェクト
   * 返値：なし
   * 指定されたDataflowオブジェクトを空にします。
   * 受け取り待ちのタスクについては何もしません。

* cc:dataflow-connect (df event-sym &optional callback)
   * 引数：
      * df: Dataflowオブジェクト
      * event-sym: イベント識別シンボル
      * callback: 受け取り関数
   * 返値：Deferredオブジェクト
   * このDataflowオブジェクトのチャンネルにシグナル受け取りタスクを追加します。
   * 内部で cc:signal-connect を呼びます。
   * 受け取れるイベント識別シンボルについては、 cc:dataflow-environment を参照してください。


* * * * *

(C) 2011  SAKURAI Masashi  All rights reserved.
m.sakurai at kiwanami.net
